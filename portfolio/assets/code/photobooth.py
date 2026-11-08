#!/usr/bin/env python3
"""
Raspberry Pi Photo Booth (2000s girly pop edition)
Click the mouse anywhere to take a strip of 4 colour photos with a countdown.
The screen shows the camera through a glittery window, surrounded by
Y2K stickers: butterflies, a flip phone, lip gloss, a pocket pet and sparkles.

Saved to ~/photobooth
Close it with Ctrl+C in the SSH window, or: pkill -f photobooth.py
"""

import math
import os
import random
from datetime import datetime

import numpy as np
from PIL import Image, ImageDraw, ImageFilter, ImageFont, ImageOps
from libcamera import Transform
from picamera2 import Picamera2
from picamera2.previews.qt import QGlPicamera2, QPicamera2
from PyQt5.QtCore import Qt, QTimer
from PyQt5.QtGui import QPixmap
from PyQt5.QtWidgets import QApplication, QLabel, QStackedWidget, QVBoxLayout, QWidget

# ---------------- Settings you can change ----------------
FOOTER_TEXT = "girly pop"      # big title at the bottom of the strip
SCREEN_TITLE = "photo booth"   # title at the top of the screen
NUM_PHOTOS = 4                 # photos per strip
COUNTDOWN = 3                  # seconds of countdown before each photo
PAUSE_BETWEEN_MS = 1500        # pause between photos
SHOW_STRIP_MS = 8000           # how long the finished strip is shown
SAVE_DIR = os.path.expanduser("~/photobooth")
PHOTO_SIZE = (1640, 1232)      # camera resolution used for the photos
MIRROR_PREVIEW = True          # preview acts like a mirror; saved photos are not mirrored
USE_OPENGL = True              # set to False if the preview stays black
# ---------------------------------------------------------

OVERLAY_SIZE = (1280, 960)     # same 4:3 shape as the camera image
LILAC = (233, 214, 255)
PINK = (247, 150, 214)
HOT_PINK = (232, 40, 150)
DEEP_PURPLE = (74, 30, 120)
GLITTER = [(255, 64, 170), (232, 30, 140), (255, 140, 210), (200, 40, 160), (255, 220, 245), (190, 90, 255)]

FONT_DIR = os.path.expanduser("~/fonts")
Y2K_FONT = os.path.join(FONT_DIR, "Audiowide-Regular.ttf")
SCRIPT_FONT = os.path.join(FONT_DIR, "Pacifico-Regular.ttf")
FALLBACK_FONT = "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf"


def load_font(path, size):
    for candidate in (path, FALLBACK_FONT):
        try:
            return ImageFont.truetype(candidate, size)
        except OSError:
            continue
    return ImageFont.load_default()


# ---------------- Basic shapes ----------------
def gradient(size, top, bottom):
    w, h = size
    t = np.linspace(0, 1, h, dtype=np.float32)[:, None, None]
    a = (1 - t) * np.array(top, np.float32) + t * np.array(bottom, np.float32)
    a = np.repeat(a, w, axis=1)
    return Image.fromarray(a.astype(np.uint8)).convert("RGBA")


def heart_points(box, n=240):
    """Points of a heart shape that fills box = (x0, y0, x1, y1)."""
    t = np.linspace(0, 2 * math.pi, n)
    x = 16 * np.sin(t) ** 3
    y = -(13 * np.cos(t) - 5 * np.cos(2 * t) - 2 * np.cos(3 * t) - np.cos(4 * t))
    x0, y0, x1, y1 = box
    x = x0 + (x - x.min()) / (x.max() - x.min()) * (x1 - x0)
    y = y0 + (y - y.min()) / (y.max() - y.min()) * (y1 - y0)
    return list(zip(x, y))


def window_box(size):
    """Where the photo window sits inside a 4:3 frame (same crop on screen and on the strip)."""
    w, h = size
    return (w * 0.14, h * 0.13, w * 0.86, h * 0.875)


def window_radius(box):
    return (box[3] - box[1]) * 0.14


def window_mask(size, box):
    mask = Image.new("L", size, 0)
    ImageDraw.Draw(mask).rounded_rectangle(box, radius=window_radius(box), fill=255)
    return mask


def glitter_ring(size, box, width, seed=1):
    """Sparkly pink glitter outline around the photo window."""
    w, h = size
    ring = Image.new("L", size, 0)
    half = width / 2
    outer = (box[0] - half, box[1] - half, box[2] + half, box[3] + half)
    ImageDraw.Draw(ring).rounded_rectangle(outer, radius=window_radius(box) + half,
                                           outline=255, width=int(width))
    rng = np.random.default_rng(seed)
    palette = np.array(GLITTER, np.float32)
    colours = palette[rng.integers(0, len(palette), (h, w))]
    colours *= rng.uniform(0.75, 1.15, (h, w, 1))
    sparkle = rng.random((h, w)) > 0.985
    colours[sparkle] = 255
    layer = Image.fromarray(np.clip(colours, 0, 255).astype(np.uint8)).convert("RGBA")
    glow = Image.new("RGBA", size, (255, 120, 210, 0))
    glow.putalpha(ring.filter(ImageFilter.GaussianBlur(width * 0.6)).point(lambda v: int(v * 0.9)))
    layer.putalpha(ring)
    return Image.alpha_composite(glow, layer)


def corner_hearts(img, box, size):
    """Little hearts sitting on the four corners of the window."""
    d = ImageDraw.Draw(img)
    inset = window_radius(box) * 0.3
    for x, y in ((box[0] + inset, box[1] + inset), (box[2] - inset, box[1] + inset),
                 (box[0] + inset, box[3] - inset), (box[2] - inset, box[3] - inset)):
        heart_shape(d, x, y, size * 1.25, (255, 255, 255, 255))
        heart_shape(d, x, y, size, HOT_PINK + (255,))


def sparkle(draw, cx, cy, size, fill=(255, 255, 255, 255)):
    s, t = size / 2, size / 12
    draw.polygon([(cx, cy - s), (cx + t, cy - t), (cx + s, cy), (cx + t, cy + t),
                  (cx, cy + s), (cx - t, cy + t), (cx - s, cy), (cx - t, cy - t)], fill=fill)


def heart_shape(draw, cx, cy, size, fill):
    draw.polygon(heart_points((cx - size / 2, cy - size * 0.45, cx + size / 2, cy + size * 0.45), 80), fill=fill)


# ---------------- Y2K stickers ----------------
def sticker(img, s, pos, angle):
    """Rotate a sticker, give it a soft shadow and paste it centred at pos."""
    s = s.rotate(angle, expand=True, resample=Image.BICUBIC)
    shadow = Image.new("RGBA", s.size, (90, 20, 110, 0))
    shadow.putalpha(s.split()[3].filter(ImageFilter.GaussianBlur(6)).point(lambda v: int(v * 0.35)))
    x, y = int(pos[0] - s.width / 2), int(pos[1] - s.height / 2)
    for layer, offset in ((shadow, (x + 5, y + 8)), (s, (x, y))):
        full = Image.new("RGBA", img.size, (0, 0, 0, 0))
        full.paste(layer, offset)          # paste copes with stickers hanging off the edge
        img.alpha_composite(full)


def butterfly(size, wing1, wing2):
    s = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    d = ImageDraw.Draw(s)
    c, u = size / 2, size / 100
    outline = DEEP_PURPLE + (255,)
    for side in (-1, 1):
        d.ellipse(sorted_box(c + side * 4 * u, 10 * u, c + side * 46 * u, 52 * u), fill=wing1 + (255,), outline=outline, width=int(2.5 * u))
        d.ellipse(sorted_box(c + side * 4 * u, 46 * u, c + side * 36 * u, 84 * u), fill=wing2 + (255,), outline=outline, width=int(2.5 * u))
        d.ellipse(sorted_box(c + side * 16 * u, 22 * u, c + side * 32 * u, 38 * u), fill=(255, 255, 255, 200))
        d.ellipse(sorted_box(c + side * 12 * u, 58 * u, c + side * 24 * u, 70 * u), fill=wing1 + (255,))
        d.line([(c, 18 * u), (c + side * 14 * u, 3 * u)], fill=outline, width=int(2.5 * u))
    d.rounded_rectangle((c - 5 * u, 14 * u, c + 5 * u, 86 * u), radius=int(5 * u), fill=outline)
    return s


def sorted_box(x0, y0, x1, y1):
    return (min(x0, x1), min(y0, y1), max(x0, x1), max(y0, y1))


def flip_phone(size):
    w, h = int(size * 0.55), size
    s = Image.new("RGBA", (w, h), (0, 0, 0, 0))
    d = ImageDraw.Draw(s)
    u = w / 100
    body, edge = (246, 120, 200, 255), DEEP_PURPLE + (255,)
    d.rounded_rectangle((4 * u, 4 * u, 96 * u, 88 * u), radius=int(16 * u), fill=body, outline=edge, width=int(3 * u))
    d.rounded_rectangle((16 * u, 16 * u, 84 * u, 74 * u), radius=int(8 * u), fill=(120, 230, 230, 255), outline=edge, width=int(3 * u))
    d.rectangle((24 * u, 24 * u, 76 * u, 66 * u), fill=(250, 230, 120, 255))
    heart_shape(d, 50 * u, 46 * u, 26 * u, (140, 60, 200, 255))
    d.rounded_rectangle((4 * u, 92 * u, 96 * u, 178 * u), radius=int(16 * u), fill=body, outline=edge, width=int(3 * u))
    for row in range(4):
        for col in range(3):
            x, y = 24 * u + col * 26 * u, 112 * u + row * 16 * u
            d.ellipse((x - 7 * u, y - 5 * u, x + 7 * u, y + 5 * u), fill=(90, 210, 220, 255), outline=edge, width=int(1.5 * u))
    d.ellipse((38 * u, 96 * u, 62 * u, 108 * u), fill=(250, 230, 120, 255), outline=edge, width=int(2 * u))
    return s


def lip_gloss(size):
    w, h = int(size * 0.32), size
    s = Image.new("RGBA", (w, h), (0, 0, 0, 0))
    d = ImageDraw.Draw(s)
    u = w / 100
    edge = DEEP_PURPLE + (255,)
    d.rounded_rectangle((10 * u, 2 * u, 90 * u, 70 * u), radius=int(12 * u), fill=(250, 220, 120, 255), outline=edge, width=int(4 * u))
    for k in range(5):
        d.line([(14 * u, (12 + k * 12) * u), (86 * u, (12 + k * 12) * u)], fill=(220, 170, 70, 255), width=int(3 * u))
    d.rounded_rectangle((6 * u, 66 * u, 94 * u, 300 * u), radius=int(22 * u), fill=(250, 170, 225, 255), outline=edge, width=int(4 * u))
    d.rounded_rectangle((22 * u, 110 * u, 78 * u, 285 * u), radius=int(18 * u), fill=(235, 80, 170, 255))
    heart_shape(d, 50 * u, 160 * u, 44 * u, (255, 255, 255, 230))
    sparkle(d, 40 * u, 230 * u, 30 * u, (255, 255, 255, 230))
    return s


def pocket_pet(size):
    s = Image.new("RGBA", (size, int(size * 1.15)), (0, 0, 0, 0))
    d = ImageDraw.Draw(s)
    u = size / 100
    edge = DEEP_PURPLE + (255,)
    for k in range(8):   # little bead chain
        d.ellipse((47 * u - 3 * u + math.sin(k) * 4 * u, k * 3 * u, 47 * u + 3 * u + math.sin(k) * 4 * u, k * 3 * u + 6 * u), fill=(255, 190, 230, 255))
    d.ellipse((6 * u, 20 * u, 94 * u, 112 * u), fill=(225, 205, 255, 255), outline=edge, width=int(3 * u))
    d.rounded_rectangle((28 * u, 40 * u, 72 * u, 76 * u), radius=int(6 * u), fill=(200, 230, 210, 255), outline=edge, width=int(3 * u))
    d.ellipse((40 * u, 50 * u, 60 * u, 68 * u), fill=(120, 90, 160, 255))   # tiny pet
    d.ellipse((44 * u, 55 * u, 48 * u, 59 * u), fill=(255, 255, 255, 255))
    d.ellipse((52 * u, 55 * u, 56 * u, 59 * u), fill=(255, 255, 255, 255))
    for x in (34, 50, 66):
        d.ellipse(((x - 6) * u, 84 * u, (x + 6) * u, 96 * u), fill=(250, 150, 220, 255), outline=edge, width=int(2 * u))
    return s


# ---------------- Bubbly gradient text ----------------
def y2k_text(img, text, font, cx, cy, top=(170, 245, 255), bottom=(190, 160, 255)):
    """Chrome-candy text: gradient fill, dark purple outline, hot pink drop shadow."""
    scratch = ImageDraw.Draw(Image.new("L", (1, 1)))
    box = scratch.textbbox((0, 0), text, font=font, stroke_width=6)
    tw, th = box[2] - box[0], box[3] - box[1]
    pad = 30
    size = (tw + 2 * pad, th + 2 * pad)
    origin = (pad - box[0], pad - box[1])

    def mask(stroke):
        m = Image.new("L", size, 0)
        ImageDraw.Draw(m).text(origin, text, font=font, fill=255, stroke_width=stroke, stroke_fill=255)
        return m

    outer, inner = mask(6), mask(0)
    shadow = Image.new("RGBA", size, HOT_PINK + (0,))
    shadow.putalpha(outer)
    layer = Image.new("RGBA", (size[0] + 10, size[1] + 12), (0, 0, 0, 0))
    layer.alpha_composite(shadow, (8, 10))
    stroke = Image.new("RGBA", size, DEEP_PURPLE + (0,))
    stroke.putalpha(outer)
    layer.alpha_composite(stroke, (0, 0))
    fill = gradient(size, top, bottom)
    fill.putalpha(inner)
    layer.alpha_composite(fill, (0, 0))
    shine = Image.new("RGBA", size, (255, 255, 255, 0))
    shine_mask = Image.new("L", size, 0)
    ImageDraw.Draw(shine_mask).rectangle((0, 0, size[0], origin[1] + th * 0.28), fill=110)
    shine.putalpha(Image.fromarray(np.minimum(np.asarray(shine_mask), np.asarray(inner))))
    layer.alpha_composite(shine, (0, 0))
    full = Image.new("RGBA", img.size, (0, 0, 0, 0))
    full.paste(layer, (int(cx - size[0] / 2), int(cy - size[1] / 2)))
    img.alpha_composite(full)


# ---------------- On-screen overlay ----------------
_screen_base = None


def screen_base():
    """Everything around the heart window. Built once, then reused."""
    global _screen_base
    if _screen_base is not None:
        return _screen_base
    w, h = OVERLAY_SIZE
    box = window_box(OVERLAY_SIZE)
    frame = gradient(OVERLAY_SIZE, LILAC, PINK)
    hole = ImageOps.invert(window_mask(OVERLAY_SIZE, box))
    base = Image.new("RGBA", OVERLAY_SIZE, (0, 0, 0, 0))
    base.paste(frame, (0, 0), hole)

    d = ImageDraw.Draw(base)
    rnd = random.Random(3)
    for _ in range(90):
        x, y = rnd.uniform(0, w), rnd.uniform(0, h)
        if hole.getpixel((int(min(x, w - 1)), int(min(y, h - 1)))) > 0:
            d.ellipse((x - 2, y - 2, x + 2, y + 2), fill=(255, 255, 255, 220))
    base.alpha_composite(glitter_ring(OVERLAY_SIZE, box, w * 0.028))
    corner_hearts(base, box, 46)

    sticker(base, lip_gloss(250), (95, 230), -32)
    sticker(base, pocket_pet(175), (w - 115, 300), 14)
    sticker(base, flip_phone(300), (120, h - 190), 24)
    sticker(base, butterfly(140, (150, 230, 120), (90, 200, 220)), (w - 175, h - 255), -18)
    sticker(base, butterfly(125, (90, 200, 220), (240, 130, 210)), (w - 85, h - 120), 12)
    sticker(base, butterfly(105, (240, 130, 210), (190, 150, 255)), (w - 235, h - 90), -6)
    d = ImageDraw.Draw(base)
    for x, y, s in ((w - 210, 70, 110), (w - 120, 160, 60), (230, 420, 70), (60, 540, 50),
                    (w - 60, 520, 55), (330, 880, 60)):
        sparkle(d, x, y, s)
    y2k_text(base, SCREEN_TITLE, load_font(Y2K_FONT, 64), w / 2, 62)
    _screen_base = base
    return base


def make_overlay(number="", label="", flash=False):
    if flash:
        return np.array(Image.new("RGBA", OVERLAY_SIZE, (255, 255, 255, 240)))
    w, h = OVERLAY_SIZE
    img = screen_base().copy()
    if number:
        y2k_text(img, number, load_font(Y2K_FONT, 300), w / 2, h * 0.5,
                 top=(255, 255, 255), bottom=(255, 170, 230))
    if label:
        font = load_font(Y2K_FONT, 40)
        d = ImageDraw.Draw(img)
        box = d.textbbox((0, 0), label, font=font)
        lw, lh = box[2] - box[0] + 120, 84
        x0, y0 = (w - lw) / 2, h - lh - 18
        d.rounded_rectangle((x0, y0, x0 + lw, y0 + lh), radius=lh / 2, fill=HOT_PINK + (255,),
                            outline=(255, 255, 255, 255), width=5)
        d.text((w / 2, y0 + lh / 2), label, font=font, fill=(255, 255, 255, 255), anchor="mm")
        heart_shape(d, x0 + 34, y0 + lh / 2, 30, (255, 255, 255, 255))
        heart_shape(d, x0 + lw - 34, y0 + lh / 2, 30, (255, 255, 255, 255))
    return np.array(img)


# ---------------- The strip ----------------
def build_strip(photos, path, when):
    margin, gap = 72, 30
    cell_w = 500
    x0, y0, x1, y1 = window_box(photos[0].size)
    cell_h = int(cell_w * (y1 - y0) / (x1 - x0))
    footer_h = 250
    strip_w = cell_w + 2 * margin
    strip_h = margin + len(photos) * cell_h + (len(photos) - 1) * gap + footer_h

    strip = gradient((strip_w, strip_h), LILAC, PINK)
    d = ImageDraw.Draw(strip)
    rnd = random.Random(8)
    for _ in range(160):
        x, y = rnd.uniform(0, strip_w), rnd.uniform(0, strip_h)
        r = rnd.uniform(1.5, 3.5)
        d.ellipse((x - r, y - r, x + r, y + r), fill=(255, 255, 255, 200))

    pad = 20
    cell_box = (pad, pad, pad + cell_w, pad + cell_h)
    canvas = (cell_w + 2 * pad, cell_h + 2 * pad)
    mask = window_mask(canvas, cell_box)
    ring = glitter_ring(canvas, cell_box, cell_w * 0.03)
    for i, photo in enumerate(photos):
        y = margin + i * (cell_h + gap)
        crop = photo.convert("RGB").crop(tuple(int(v) for v in window_box(photo.size)))
        framed = Image.new("RGB", canvas)
        framed.paste(crop.resize((cell_w, cell_h), Image.LANCZOS), (pad, pad))
        strip.paste(framed, (margin - pad, y - pad), mask)
        strip.alpha_composite(ring, (margin - pad, y - pad))
        corner_hearts(strip, (margin, y, margin + cell_w, y + cell_h), 30)

    # Stickers in the side margins, so they never cover faces
    L, R = margin * 0.5, strip_w - margin * 0.5
    row = lambda i, f: margin + i * (cell_h + gap) + cell_h * f
    sticker(strip, butterfly(90, (150, 230, 120), (90, 200, 220)), (L, row(0, 0.85)), -15)
    sticker(strip, lip_gloss(150), (R, row(0, 0.45)), 20)
    sticker(strip, butterfly(80, (240, 130, 210), (190, 150, 255)), (R, row(1, 0.9)), 14)
    sticker(strip, pocket_pet(90), (L, row(2, 0.45)), -12)
    sticker(strip, flip_phone(160), (R, row(3, 0.55)), 14)
    sticker(strip, butterfly(80, (90, 200, 220), (240, 130, 210)), (L, row(3, 0.15)), 8)
    d = ImageDraw.Draw(strip)
    for x, y, sz in ((R, 26, 44), (L, row(1, 0.3), 40), (R, row(2, 0.2), 38),
                     (L, strip_h - 70, 46), (R, strip_h - 60, 52)):
        sparkle(d, x, y, sz)

    footer_top = strip_h - footer_h
    y2k_text(strip, FOOTER_TEXT, load_font(Y2K_FONT, 72), strip_w / 2, footer_top + 105)
    d.text((strip_w / 2, footer_top + 190), when.strftime("%d.%m.%Y"), font=load_font(SCRIPT_FONT, 38),
           fill=DEEP_PURPLE + (255,), anchor="mm")
    strip.convert("RGB").save(path, quality=95)


# ---------------- The app ----------------
class PhotoBooth(QWidget):
    def __init__(self, picam2):
        super().__init__()
        self.picam2 = picam2
        self.busy = False
        self.photos = []
        self.count = 0

        preview_class = QGlPicamera2 if USE_OPENGL else QPicamera2
        self.preview = preview_class(picam2, keep_ar=True, bg_colour=PINK)
        self.preview.done_signal.connect(self.photo_taken)

        self.strip_label = QLabel()
        self.strip_label.setAlignment(Qt.AlignCenter)

        self.stack = QStackedWidget()
        self.stack.addWidget(self.preview)
        self.stack.addWidget(self.strip_label)

        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.addWidget(self.stack)
        self.setStyleSheet("background-color: #F796D6;")

        self.show_idle()

    def show_idle(self):
        self.stack.setCurrentWidget(self.preview)
        self.preview.set_overlay(make_overlay(label="click to start!"))
        self.busy = False

    def mousePressEvent(self, event):
        if not self.busy:
            self.busy = True
            self.photos = []
            self.next_photo()

    def keyPressEvent(self, event):
        if event.key() == Qt.Key_Escape:
            self.close()

    def next_photo(self):
        self.count = COUNTDOWN
        self.tick()

    def tick(self):
        if self.count > 0:
            label = f"photo {len(self.photos) + 1} of {NUM_PHOTOS}"
            self.preview.set_overlay(make_overlay(str(self.count), label))
            self.count -= 1
            QTimer.singleShot(1000, self.tick)
        else:
            self.preview.set_overlay(make_overlay(flash=True))
            self.picam2.capture_image("main", signal_function=self.preview.signal_done)

    def photo_taken(self, job):
        photo = self.picam2.wait(job)
        if MIRROR_PREVIEW:
            photo = ImageOps.mirror(photo)
        self.photos.append(photo.convert("RGB"))

        if len(self.photos) < NUM_PHOTOS:
            self.preview.set_overlay(make_overlay(label="strike a pose!"))
            QTimer.singleShot(PAUSE_BETWEEN_MS, self.next_photo)
        else:
            self.preview.set_overlay(make_overlay(label="making your strip..."))
            QTimer.singleShot(100, self.finish_strip)   # let the label appear first

    def finish_strip(self):
        when = datetime.now()
        stamp = when.strftime("%Y%m%d-%H%M%S")
        for i, photo in enumerate(self.photos, 1):
            photo.save(os.path.join(SAVE_DIR, f"{stamp}-{i}.jpg"), quality=95)

        strip_path = os.path.join(SAVE_DIR, f"{stamp}-strip.jpg")
        build_strip(self.photos, strip_path, when)

        pixmap = QPixmap(strip_path).scaled(self.size(), Qt.KeepAspectRatio,
                                            Qt.SmoothTransformation)
        self.strip_label.setPixmap(pixmap)
        self.stack.setCurrentWidget(self.strip_label)
        QTimer.singleShot(SHOW_STRIP_MS, self.show_idle)


def main():
    os.makedirs(SAVE_DIR, exist_ok=True)

    picam2 = Picamera2()
    config = picam2.create_preview_configuration(
        main={"size": PHOTO_SIZE},
        transform=Transform(hflip=MIRROR_PREVIEW),
    )
    picam2.configure(config)

    app = QApplication([])
    booth = PhotoBooth(picam2)
    app.setOverrideCursor(Qt.BlankCursor)
    booth.showFullScreen()

    picam2.start()
    app.exec_()
    picam2.stop()


if __name__ == "__main__":
    main()
