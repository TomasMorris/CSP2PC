#!/usr/bin/env python3

from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import io
import math
import os
import shutil
import sqlite3
import struct
import sys
import tempfile
import time
import uuid
import zipfile
from pathlib import Path
from typing import List
from plistlib import UID
import plistlib
import tkinter as tk
from tkinter import filedialog
from PIL import Image, ImageChops, ImageOps, ImageFilter

# ---------------------------------------------------------------------------
# Helper constants -----------------------------------------------------------
# ---------------------------------------------------------------------------

IEND_MARKER = b"IEND"
SQLITE_MAGIC = b"SQLite format 3"  

# ---------------------------------------------------------------------------
# Stage 1 - PNG extraction helpers -------------------------------------------
# ---------------------------------------------------------------------------

def prepare_shape(src: Path, dest: Path, is_procedural: bool = False) -> None:
    """
    Convert CSP stamp → Procreate tip.
    For procedural tips, the image is already in the correct L-mode format.
    For stamp tips, convert RGBA → invert → multiply by alpha.
    """
    if is_procedural:
        # Procedural tips are already generated as L-mode grayscale
        Image.open(src).convert("L").save(dest, format="PNG")
        return
    # Existing stamp conversion: RGBA → invert → multiply by alpha
    im = Image.open(src).convert("RGBA")
    r, g, b, a = im.split()
    gray = Image.merge("RGB", (r, g, b)).convert("L")
    inv = ImageOps.invert(gray)
    mask = ImageChops.multiply(inv, a)

    mask.save(dest, format="PNG")   # L-mode PNG

def locate_sqlite_offset(data: bytes) -> int:
    off = data.find(SQLITE_MAGIC)
    if off == -1:
        raise ValueError("SQLite header not found — is this a .sut file?")
    return off

def dump_sqlite_blob(sut_path: Path) -> Path:
    raw = sut_path.read_bytes()
    off = locate_sqlite_offset(raw)
    tmp = Path(tempfile.mktemp(suffix=".sqlite"))
    tmp.write_bytes(raw[off:])
    return tmp

def detect_brush_type(sqlite_path: Path) -> str:
    """
    Determine whether a .sut file contains a procedural or stamp-based brush.

    Returns:
        "procedural" — tip defined by BrushHardness, no custom images
        "stamp"      — custom PNG stamp(s) in MaterialFile table
    """
    con = sqlite3.connect(sqlite_path)
    cur = con.cursor()

    # Check if MaterialFile table exists
    tables = [t[0] for t in cur.execute(
        "SELECT name FROM sqlite_master WHERE type='table'"
    ).fetchall()]
    has_material = "MaterialFile" in tables

    # Check BrushUsePatternImage flag in Variant table
    try:
        use_pattern = cur.execute(
            "SELECT BrushUsePatternImage FROM Variant LIMIT 1"
        ).fetchone()
        uses_pattern = bool(use_pattern and use_pattern[0])
    except sqlite3.OperationalError:
        uses_pattern = False

    con.close()

    if has_material and uses_pattern:
        return "stamp"

    # Default to procedural — tip generated from BrushHardness
    return "procedural"

def generate_procedural_tip(hardness: int, thickness: int = 100,
                            size_px: int = 2048) -> Image.Image:
    """
    Generate a grayscale brush tip image from CSP's BrushHardness parameter.

    In Procreate, hardness is baked into the Shape.png image as a radial gradient.
    CSP's BrushHardness (0-100) controls the falloff from center to edge:
      - 100 = sharp circle (step function at radius)
      - 0   = very soft gaussian-like falloff

    BrushThickness (0-100) controls vertical scaling:
      - 100 = perfect circle
      - 50  = ellipse at 50% height

    Returns an L-mode (grayscale) PIL Image, size_px × size_px.
    White center (255) fades to black edge (0) — Procreate convention.
    """
    img = Image.new("L", (size_px, size_px), 0)
    pixels = img.load()

    center_x = size_px / 2.0
    center_y = size_px / 2.0
    radius = size_px / 2.0

    # Thickness scales the vertical radius (100 = circle, <100 = ellipse)
    y_scale = max(thickness, 1) / 100.0

    # Hardness controls the falloff curve exponent
    if hardness >= 100:
        exponent = 50.0   # effectively a step function
    elif hardness <= 0:
        exponent = 0.4    # very soft falloff
    else:
        # Map 0-100 → 0.4-50.0 with a curve that emphasises the middle range
        t = hardness / 100.0
        exponent = 0.4 + (50.0 - 0.4) * (t ** 1.5)

    for y in range(size_px):
        for x in range(size_px):
            dx = (x - center_x) / radius
            dy = (y - center_y) / (radius * y_scale) if y_scale > 0 else 0
            dist = math.sqrt(dx * dx + dy * dy)

            if dist >= 1.0:
                value = 0
            else:
                value = int(255 * ((1.0 - dist) ** (1.0 / exponent)))
                value = max(0, min(255, value))

            pixels[x, y] = value

    return img

def _extract_png_from_layer(blob: bytes) -> bytes:
    pos_png = blob.rfind(b"PNG")
    if pos_png <= 0:
        raise RuntimeError("PNG signature not found in layer blob")
    begin = pos_png - 1
    pos_iend = blob.rfind(IEND_MARKER)
    if pos_iend == -1:
        raise RuntimeError("IEND marker not found in layer blob")
    end = pos_iend + 4
    return blob[begin:end]

def get_seed_path() -> Path:
    if getattr(sys, 'frozen', False):
        base = Path(sys._MEIPASS)
    else:
        base = Path(__file__).parent
    return base / "Seed.brush"

def write_quicklook_thumbnail(bundle_dir: Path, original_stamp_png: Path,
                               is_procedural: bool = False) -> None:
    ql_dir = bundle_dir / "QuickLook"
    ql_dir.mkdir(exist_ok=True)
    thumb_w, thumb_h = 1060, 324
    bg = Image.new("RGBA", (thumb_w, thumb_h), (0, 0, 0, 0))

    if is_procedural:
        # Stroke preview: stamp the tip multiple times along a horizontal line
        tip = Image.open(original_stamp_png).convert("L")
        tip_size = int(thumb_h * 0.6)
        tip = tip.resize((tip_size, tip_size), Image.LANCZOS)
        tip_rgba = Image.new("RGBA", tip.size, (0, 0, 0, 0))
        tip_rgba.putalpha(tip)
        margin = tip_size // 2
        spacing = max(tip_size // 4, 2)
        y_pos = (thumb_h - tip_size) // 2
        for x in range(margin, thumb_w - margin, spacing):
            bg.alpha_composite(tip_rgba, (x - tip_size // 2, y_pos))
    else:
        stamp = Image.open(original_stamp_png).convert("RGBA")
        scale = thumb_h / stamp.height
        new_w = int(stamp.width * scale)
        new_h = int(stamp.height * scale)
        stamp = stamp.resize((new_w, new_h), Image.LANCZOS)
        x_pos = (thumb_w - new_w) // 2
        y_pos = (thumb_h - new_h) // 2
        bg.alpha_composite(stamp, (x_pos, y_pos))

    (ql_dir / "Thumbnail.png").write_bytes(b"")
    bg.save(ql_dir / "Thumbnail.png", "PNG")
    
def pick_files():
    root = tk.Tk()
    root.withdraw()
    sut_path = filedialog.askopenfilename(
        title="Select CSP Brush (.sut)",
        filetypes=[("CSP Brush", "*.sut"), ("CSP Brush Group", "*.sutg"),
                   ("All files", "*.*")]
    )
    if not sut_path:
        sys.exit("No .sut selected.")

    dest_dir = filedialog.askdirectory(title="Select Output Folder")
    if not dest_dir:
        sys.exit("No output folder selected.")
    return Path(sut_path), Path(dest_dir)

def extract_pngs_from_sut(sut_path: Path, dest_dir: Path) -> List[Path]:
    dest_dir.mkdir(parents=True, exist_ok=True)
    sqlite_tmp = dump_sqlite_blob(sut_path)

    paths: List[Path] = []
    try:
        con = sqlite3.connect(sqlite_tmp)
        cur = con.cursor()

        try:
            rows = cur.execute("SELECT _PW_ID, FileData FROM MaterialFile").fetchall()
        except sqlite3.OperationalError:
            # Table not found — unusual .sut layout
            return []

        if not rows:
            return []

        for idx, (_id, blob) in enumerate(rows):
            try:
                png_bytes = _extract_png_from_layer(blob)
                path = dest_dir / f"stamp_{idx:02d}.png"
                path.write_bytes(png_bytes)
                paths.append(path)
            except Exception as exc:
                print(f"[WARN] layer {_id} skipped: {exc}")

    finally:
        try:
            cur.close()
            con.close()
        except Exception:
            pass
        sqlite_tmp.unlink(missing_ok=True)

    return paths
def extract_texture_image(sqlite_path: Path, dest: Path) -> Path | None:
    """
    Extract TextureImage blob from Variant table and save as PNG.

    CSP stores texture/paper images in the TextureImage column as raw image data.
    In Procreate, this maps to Signature/SignaturePicture.png (the grain texture).

    Returns the path to the extracted texture, or None if no texture exists.
    """
    con = sqlite3.connect(sqlite_path)
    cur = con.cursor()

    try:
        row = cur.execute("SELECT TextureImage FROM Variant LIMIT 1").fetchone()
        if row is None or row[0] is None or len(row[0]) == 0:
            return None

        blob = row[0]

        # TextureImage blob may contain raw image data with a PNG signature
        png_start = blob.find(b"\x89PNG")
        if png_start >= 0:
            iend = blob.find(b"IEND", png_start)
            if iend >= 0:
                png_data = blob[png_start:iend + 8]
                dest.write_bytes(png_data)
                return dest

        # Fallback: try to open the whole blob as an image
        try:
            img = Image.open(io.BytesIO(blob))
            img.convert("L").save(dest, "PNG")
            return dest
        except Exception:
            return None

    finally:
        con.close()
# ---------------------------------------------------------------------------
# Stage 2 - Create Brush -----------------------------------------------------
# ---------------------------------------------------------------------------

def read_variant_row(sqlite_path: Path):
    """
    Helper function to read the variant row from the .sut (sql) database
    """
    con = sqlite3.connect(sqlite_path)
    row = con.execute("SELECT * FROM Variant LIMIT 1").fetchone()
    names = [d[1] for d in con.execute("PRAGMA table_info('Variant')")]
    con.close()
    return dict(zip(names, row))
    
def csp_to_plotSpacing(variant):
    size_px     = variant.get("BrushSize", 1) or 1
    interval_px = variant.get("BrushInterval", 0) or 0

    if size_px <= 0:
        return 0.01
    raw_spacing = interval_px / size_px

    # Adjust fudge factor: larger brushes can have higher spacing multipliers
    if size_px < 50:
        fudge_factor = 0.15
    elif size_px < 100:
        fudge_factor = 0.3
    else:
        fudge_factor = 0.6

    adjusted_spacing = raw_spacing * fudge_factor
    return max(0.01, min(1.0, adjusted_spacing))


def map_csp_rendering_flags(variant):
    """
    Helper function to somewhat map to procreates rendering settings
    """
    use_watercolor = bool(variant.get("BrushUseWaterColor", 0))
    mix_color      = float(variant.get("BrushMixColor", 0.0) or 0)
    mix_alpha      = float(variant.get("BrushMixAlpha", 0.0) or 0)
    brush_flow     = float(variant.get("BrushFlow", 1.0) or 1.0)

    # -- Light Glaze --
    flags = {
        "renderingMaxTransfer": True,
        "renderingModulatedTransfer": False,
        "renderingRecursiveMixing": False,
    }

    if use_watercolor or mix_color > 0.05 or mix_alpha > 0.05:
        flags["renderingRecursiveMixing"] = True

        if mix_color >= 0.75 or mix_alpha >= 0.75:
            # Intense Glaze
            flags["renderingMaxTransfer"] = True
            flags["renderingModulatedTransfer"] = True
        elif brush_flow > 0.8:
            # Heavy Glaze
            flags["renderingMaxTransfer"] = True
            flags["renderingModulatedTransfer"] = False
        else:
            # Uniform Blending
            flags["renderingMaxTransfer"] = False
            flags["renderingModulatedTransfer"] = True

    return flags

def map_csp_to_wet_mix(variant):
    """
    Helper function to somewhat map to procreates wet-mix settings
    """
    use_wc   = bool(variant.get("BrushUseWaterColor", 0))
    mix_col  = float(variant.get("BrushMixColor", 0) or 0)
    mix_alpha= float(variant.get("BrushMixAlpha", 0) or 0)
    flow     = float(variant.get("BrushFlow", 100) or 100)
    nc = max(0.0, min(1.0, mix_col/100.0))
    na = max(0.0, min(1.0, mix_alpha/100.0))
    nf = max(0.0, min(1.0, flow/100.0))
    if not use_wc and nc < 0.5:
        dilution = 0.0
    else:
        gamma = 0.75
        cap   = 0.7
        base = nc ** gamma
        flow_brake = 0.5 + 0.5*(1.0 - nf)
        alpha_push = 0.2*na

        dilution = min(cap, base*cap*flow_brake + alpha_push*cap)

    charge = max(0.2, 1.0 - dilution)
    attack = 1.0 - 0.5*na
    pull = 0.6 if use_wc else 0.0

    return {
        "wetMixDilution": dilution,
        "wetMixCharge":   charge,
        "wetMixAttack":   attack,
        "wetMixPull":     pull,
    }


def finalise_seed_brush(bundle_dir: Path, stamp_png: Path, new_name: str,
                        sql_tmp: Path | None = None,
                        verbose: bool = False) -> None:
    """
    bundle_dir contains Brush.archive and the freshly-copied Shape.png
    stamp_png  : path to the stamp (already grayscale or not)
    new_name   : visible name in Brush Library
    sql_tmp:   : path to the .sut file to access all it's properties
    """
    Image.open(stamp_png).convert("L").save(bundle_dir / "Shape.png")

    plist_path = bundle_dir / "Brush.archive"
    root       = plistlib.load(plist_path.open("rb"))
    objs       = root["$objects"]

    def resolve(val):
        """follow UID indirection until we reach the real object"""
        while isinstance(val, UID):
            val = objs[val.data]
        return val

    # 2 ─ bump creation timestamp & rename brush
    stamped, renamed = False, False
    now = float(time.time())
    variant = read_variant_row(sql_tmp)
    spacing = csp_to_plotSpacing(variant)
    # --- Derive mapped values from CSP variant parameters ---
    # Size: CSP pixels → Procreate normalized (heuristic: /27)
    csp_size = float(variant.get("BrushSize", 30) or 30)
    max_px = max(0.01, min(12.0, csp_size / 27.0))
    # MinSize: small if pressure-sensitive, near max otherwise
    # TODO: Future work — parse BrushSizeEffector blob to extract actual
    # pressure curve and map to dynamicsPressureSizeCurve.
    has_size_effector = variant.get("BrushSizeEffector") is not None
    min_px = max_px * 0.01 if has_size_effector else max_px * 0.8
    # Opacity from CSP (0-100 → 0-1)
    opacity = float(variant.get("Opacity", 100)) / 100.0

    # Randomization: scatter mode OR spray random rotation
    BrushPatternOrderType = variant.get("BrushPatternOrderType", 0)
    randomized = bool(
        BrushPatternOrderType == 3
        or (variant.get("BrushUseSpray")
            and variant.get("BrushRotationRandomInSpray", 0) != 0)
    )
    BrushRotation = variant.get("BrushRotation")
    BrushRotationRandomScale = variant.get("BrushRotationRandomScale", 0) / 100

    # Jitter: use spray bias for positional jitter (NOT BrushRevision which is stabilisation)
    if variant.get("BrushUseSpray"):
        jitter_val = float(variant.get("BrushSprayBias", 0)) / 100.0
    else:
        jitter_val = 0.0

    BrushUseIn  = variant.get("BrushUseIn")
    BrushUseOut = variant.get("BrushUseOut")
    BrushInLength  = variant.get("BrushInLength", 0)
    BrushOutLength = variant.get("BrushOutLength", 0)
    render_flags = map_csp_rendering_flags(variant)
    wetMix_flags = map_csp_to_wet_mix(variant)
    angle_sensitive = variant.get("BrushRotationEffector") == 3

    # Flow → Procreate glazedFlow (0-1)
    flow_norm = float(variant.get("BrushFlow", 100)) / 100.0
    # Thickness → Procreate shapeRoundness (0-1)
    roundness = float(variant.get("BrushThickness", 100)) / 100.0

    if verbose:
        print(f"  [INFO] BrushSize={csp_size} → maxSize={max_px:.3f}")
        print(f"  [INFO] Opacity={variant.get('Opacity')} → maxOpacity={opacity:.2f}")
        print(f"  [INFO] BrushFlow={variant.get('BrushFlow')} → glazedFlow={flow_norm:.2f}")
        print(f"  [INFO] BrushThickness={variant.get('BrushThickness')} → roundness={roundness:.2f}")

    # TODO: Future work — parse effector blobs to extract pressure/tilt/velocity curves.
    # Effector format appears to be: 4-byte header + N control points (each ~12 bytes).
    # Sizes observed: 44 bytes (simple linear), 88 bytes (2 segments), 164 bytes (complex).
    # These should map to Procreate's ValkyrieMagnitudinalCurve 'points' array.
    effector_cols = ["BrushSizeEffector", "BrushOpacityEffector",
                     "BrushFlowEffector", "BrushThicknessEffector"]
    for col in effector_cols:
        blob = variant.get(col)
        if blob and len(blob) > 44:
            if verbose:
                print(f"  [WARN] {col} ({len(blob)} bytes) has custom curve "
                      f"— not yet parsed, using linear")

    # TODO: Future work — dual brush has no direct Procreate equivalent.
    # CSP's dual brush composites two brush engines; Procreate lacks this concept.
    # Possible approximation: use dual brush pattern as grain texture.
    if variant.get("UseDualBrush"):
        if verbose:
            print("  [WARN] Dual brush enabled in CSP — no Procreate "
                  "equivalent, skipping secondary brush")

    for obj in objs:
        if not isinstance(obj, dict):
            continue

        # (a) creationDate → NS.time
        if not stamped and ("creationDate" in obj or b"creationDate" in obj):
            cd = resolve(obj.get("creationDate") or obj.get(b"creationDate"))
            if isinstance(cd, dict) and ("NS.time" in cd or b"NS.time" in cd):
                key = "NS.time" if "NS.time" in cd else b"NS.time"
                cd[key] = now
                stamped = True

        # (b) visible name
        if not renamed and ("name" in obj or b"name" in obj):
            objs[obj.get("name")] = new_name
            renamed  = True
            
        # (c) spacing
        if "plotSpacing" in obj:
            obj["plotSpacing"] = float(spacing)
            
        # (d) minSize
        if "minSize" in obj:
            obj["minSize"] = float(min_px)
            
        # (e) maxSize
        if "maxSize" in obj:
            obj["maxSize"] = float(max_px)
            
        # (f) opacity
        if "maxOpacity" in obj:
            obj["maxOpacity"] = float(opacity)
            
        # (g) rotation
        if "shapeRotation" in obj:
            obj["shapeRotation"] = float(BrushRotation)
            
        # (h) randomized
        if "shapeRandomise" in obj:
            obj["shapeRandomise"] = bool(randomized)
            
        # (i) scatter
        if "shapeRandomise" in obj:
            if BrushPatternOrderType == 3:
                obj["shapeScatter"] = float(BrushRotationRandomScale)
            else:
                obj["shapeScatter"] = float(0)
                
        # (j) FlipX
        if "shapeFlipXJitter" in obj and BrushPatternOrderType == 3:
            obj["shapeFlipXJitter"] = True
        elif "shapeFlipXJitter" in obj and not BrushPatternOrderType == 3:
            obj["shapeFlipXJitter"] = False
            
        # (k) jitter
        if "plotJitter" in obj:
            obj["plotJitter"] = float(jitter_val)
            
        # (l) Taper
        if "taperPressure" in obj:
            obj["taperPressure"] = float(0)
        if BrushUseIn or BrushUseOut:
            if "pencilTaperStartLength" in obj:
                obj["pencilTaperStartLength"] = float((BrushInLength/100)/4)
            if "pencilTaperEndLength" in obj:
                obj["pencilTaperEndLength"] = float((BrushOutLength/100)/2)
                
        # (m) render mode
        if "renderingMaxTransfer" in obj:
            obj["renderingMaxTransfer"] = render_flags['renderingMaxTransfer']
        if "renderingModulatedTransfer" in obj:
            obj["renderingModulatedTransfer"] = render_flags['renderingModulatedTransfer']
        if "renderingRecursiveMixing" in obj:
            obj["renderingRecursiveMixing"] = render_flags['renderingRecursiveMixing']
            
        # (n) wet-mix
        if "dynamicsMix" in obj:
            obj["dynamicsMix"] = float(wetMix_flags['wetMixDilution'])
        if "dynamicsLoad" in obj:
            obj["dynamicsLoad"] = float(wetMix_flags['wetMixCharge'])
        if "dynamicsPressureMix" in obj:
            obj["dynamicsPressureMix"] = float(wetMix_flags['wetMixAttack'])
        if "dynamicsWetAccumulation" in obj:
            obj["dynamicsWetAccumulation"] = float(wetMix_flags['wetMixPull'])
            
        # (o) shape input-style for angle sensitivity
        if angle_sensitive:
            if "shapeAzimuth" in obj:
                obj["shapeAzimuth"] = True
            if "shapeRoll" in obj:
                obj["shapeRoll"] = True
            if "shapeRollMode" in obj:
                obj["shapeRollMode"] = 1
            if "shapeOrientation" in obj:
                obj["shapeOrientation"] = 1

        # (p) flow → glazedFlow
        if "dynamicsGlazedFlow" in obj:
            obj["dynamicsGlazedFlow"] = float(flow_norm)

        # (q) thickness → shapeRoundness
        if "shapeRoundness" in obj:
            obj["shapeRoundness"] = float(roundness)

        # (r) pressure-to-size sensitivity
        # TODO: Future work — parse BrushSizeEffector blob to extract
        # actual pressure curve → dynamicsPressureSizeCurve.
        if "dynamicsPressureSize" in obj:
            obj["dynamicsPressureSize"] = float(1.0 if has_size_effector else 0.0)

    plistlib.dump(root, plist_path.open("wb"), fmt=plistlib.FMT_BINARY)

def build_brush(
    shape_png: Path,
    brush_out: Path,
    seed_brush: Path,
    display_name: str | None = None,
    sql_tmp: Path | None = None,
    is_procedural: bool = False,
    verbose: bool = False,
) -> None:
    """
    Create a Procreate **.brush** by copying *seed_brush* and replacing its
    Shape.png with *shape_png*.

    Parameters
    ----------
    shape_png     The stamp you want to use (must be grayscale PNG).
    brush_out     Where to write the finished .brush file.
    seed_brush    A previously-exported brush that acts as a template.
    display_name  Optional filename shown inside Procreate’s library; if None
                  we derive it from `brush_out.stem`.
    sql_tmp        Path of the .sut file to access further brush properties.
    is_procedural  True if the brush tip was procedurally generated.
    verbose        Print detailed conversion info.
    """
    tmp_dir = brush_out.parent / f".tmp_{uuid.uuid4().hex}"
    tmp_dir.mkdir(parents=True, exist_ok=True)

    # 1. Unzip seed into temp dir
    with zipfile.ZipFile(seed_brush) as z:
        z.extractall(tmp_dir)

    # 2. Prepare the brush stamp and edit its properties
    tmp_shape = tmp_dir / "Shape.png"
    write_quicklook_thumbnail(tmp_dir, shape_png, is_procedural=is_procedural)
    prepare_shape(shape_png, tmp_shape, is_procedural=is_procedural)

    # Apply texture image from .sut as grain if available
    if sql_tmp:
        sig_dir = tmp_dir / "Signature"
        sig_dir.mkdir(exist_ok=True)
        grain_path = sig_dir / "SignaturePicture.png"
        extracted = extract_texture_image(sql_tmp, grain_path)
        if extracted and verbose:
            print(f"  [INFO] TextureImage extracted → grain texture applied")
        elif verbose:
            print(f"  [INFO] No TextureImage in .sut — using seed default grain")

    finalise_seed_brush(tmp_dir, tmp_shape, display_name, sql_tmp,
                        verbose=verbose)

    # 3. Re-zip → .brush (files only — Procreate crashes on directory entries)
    with zipfile.ZipFile(brush_out, "w", compression=zipfile.ZIP_DEFLATED) as z:
        for item in tmp_dir.rglob("*"):
            if item.is_file():
                z.write(item, arcname=item.relative_to(tmp_dir))

    shutil.rmtree(tmp_dir, ignore_errors=True)
    print(
        f"✓ built .brush ({shape_png.name}) → {brush_out.name}  "
        f"[{_dt.datetime.now().strftime('%H:%M:%S')}]"
    )

def build_brushset(brush_files: List[Path], set_out: Path, set_name: str) -> None:
    """
    • brush_files : list of finished .brush files (zip archives)
    • set_out     : final .brushset path
    • set_name    : name shown in Procreate’s Brush Library
    """
    tmp_set = Path(tempfile.mkdtemp())
    uuids   = []
    for bf in brush_files:
        uid = str(uuid.uuid4()).upper()
        uuids.append(uid)
        dest_dir = tmp_set / uid
        dest_dir.mkdir()

        # unzip .brush into its UUID folder
        with zipfile.ZipFile(bf) as zf:
            zf.extractall(dest_dir)
    plist_path = tmp_set / "brushset.plist"
    plist_path.write_bytes(
        plistlib.dumps({"name": set_name, "brushes": uuids}, fmt=plistlib.FMT_XML)
    )
    with zipfile.ZipFile(set_out, "w", zipfile.ZIP_DEFLATED) as z:
        for item in tmp_set.rglob("*"):
            if not item.is_file():
                continue
            z.write(item, arcname=item.relative_to(tmp_set))

    shutil.rmtree(tmp_set, ignore_errors=True)
    print(f"✓ built brush-set → {set_out.name}")

def main(argv: List[str] | None = None) -> None:
    # Ensure UTF-8 output on Windows consoles
    if sys.stdout and hasattr(sys.stdout, 'reconfigure'):
        try:
            sys.stdout.reconfigure(encoding='utf-8', errors='replace')
        except Exception:
            pass

    ap = argparse.ArgumentParser(description="CSP → Procreate converter")
    ap.add_argument("sut",  help="Input .sut file or directory of .sut files")
    ap.add_argument("dest", help="Output directory")
    ap.add_argument("-v", "--verbose", action="store_true",
                    help="Print detailed conversion info")

    if argv is None and len(sys.argv) == 1:
        sut, dest = pick_files()
        verbose = False
    else:
        args = ap.parse_args(argv)
        sut, dest = Path(args.sut), Path(args.dest)
        verbose = args.verbose

    seed = get_seed_path()
    out  = Path(dest).resolve()
    out.mkdir(parents=True, exist_ok=True)

    # Collect .sut files (single file or batch directory)
    sut_path = Path(sut).resolve()
    if sut_path.is_dir():
        sut_files = sorted(sut_path.glob("*.sut"))
        if not sut_files:
            raise SystemExit(f"No .sut files found in {sut_path}")
        print(f"Batch mode: found {len(sut_files)} .sut files")
    else:
        # TODO: .sutg support — brush group files contain multiple brushes
        # in a single container. Future work: parse .sutg structure and
        # extract individual .sut entries for conversion.
        if sut_path.suffix.lower() == ".sutg":
            sys.exit(
                "⚠ .sutg (brush group) files are not yet supported.\n"
                "  Extract individual .sut brushes from Clip Studio Paint first.\n"
                "  (File > Export > Sub Tool > select individual brushes)"
            )
        sut_files = [sut_path]

    all_built: list[Path] = []

    for sut_file in sut_files:
        print(f"\n── Converting: {sut_file.name}")
        sqlite_tmp = dump_sqlite_blob(sut_file)

        try:
            brush_type = detect_brush_type(sqlite_tmp)
            if verbose:
                print(f"  [INFO] Brush type: {brush_type}")

            try:
                variant = read_variant_row(sqlite_tmp)
            except Exception as exc:
                print(f"  [ERROR] Could not read Variant table from "
                      f"{sut_file.name}: {exc}")
                print(f"  This may not be a valid CSP brush file.")
                continue

            if brush_type == "procedural":
                # Generate tip from BrushHardness
                hardness = int(variant.get("BrushHardness", 50))
                thickness = int(variant.get("BrushThickness", 100))
                if verbose:
                    print(f"  [INFO] Generating procedural tip: "
                          f"hardness={hardness}, thickness={thickness}")

                tip_img = generate_procedural_tip(hardness, thickness)
                tip_path = out / f"{sut_file.stem}_tip.png"
                tip_img.save(tip_path, "PNG")
                pngs = [tip_path]
                is_procedural = True
            else:
                # Extract stamp PNGs from MaterialFile
                png_dir = out / sut_file.stem
                png_dir.mkdir(parents=True, exist_ok=True)
                pngs = extract_pngs_from_sut(sut_file, png_dir)
                is_procedural = False

                if not pngs:
                    print(f"  [WARN] No PNG stamps found in "
                          f"{sut_file.name}, falling back to procedural")
                    hardness = int(variant.get("BrushHardness", 50))
                    thickness = int(variant.get("BrushThickness", 100))
                    tip_img = generate_procedural_tip(hardness, thickness)
                    tip_path = out / f"{sut_file.stem}_tip.png"
                    tip_img.save(tip_path, "PNG")
                    pngs = [tip_path]
                    is_procedural = True

            # Build brush(es)
            for i, stamp in enumerate(pngs, start=1):
                if len(pngs) == 1:
                    brush_path = out / f"{sut_file.stem}.brush"
                    display_name = sut_file.stem
                else:
                    brush_path = out / f"{sut_file.stem}_{i}.brush"
                    display_name = f"{sut_file.stem} {i}"

                build_brush(
                    shape_png=stamp,
                    brush_out=brush_path,
                    seed_brush=seed,
                    display_name=display_name,
                    sql_tmp=sqlite_tmp,
                    is_procedural=is_procedural,
                    verbose=verbose,
                )
                all_built.append(brush_path)

        finally:
            sqlite_tmp.unlink(missing_ok=True)

    # Bundle all brushes into a brushset if multiple
    if len(all_built) > 1:
        set_name = sut_path.stem
        set_path = out / f"{set_name}.brushset"
        build_brushset(all_built, set_path, set_name)
        print(f"\n✓ Bundled {len(all_built)} brushes into {set_path.name}")
    elif len(all_built) == 1:
        print(f"\n✓ Generated single brush: {all_built[0].name}")
    else:
        print("\n⚠ No brushes were generated")



if __name__ == "__main__":
    main()
