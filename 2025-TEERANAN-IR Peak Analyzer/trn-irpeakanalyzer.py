import tkinter as tk
from tkinter import ttk, messagebox, simpledialog, filedialog
import numpy as np
from scipy.signal import find_peaks
from scipy.optimize import curve_fit
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.figure import Figure
import copy
import random
from io import BytesIO
from PIL import Image
import ctypes
from ctypes import wintypes

# --- 1. ENABLE HIGH DPI ---
try: ctypes.windll.shcore.SetProcessDpiAwareness(1)
except: pass

# --- 2. SAFE CLIPBOARD SETUP ---
user32 = ctypes.windll.user32
kernel32 = ctypes.windll.kernel32
user32.OpenClipboard.argtypes = [ctypes.c_void_p]
user32.EmptyClipboard.argtypes = []
user32.SetClipboardData.argtypes = [ctypes.c_uint, ctypes.c_void_p]
user32.CloseClipboard.argtypes = []
kernel32.GlobalAlloc.argtypes = [ctypes.c_uint, ctypes.c_size_t]
kernel32.GlobalAlloc.restype = ctypes.c_void_p
kernel32.GlobalLock.argtypes = [ctypes.c_void_p]
kernel32.GlobalLock.restype = ctypes.c_void_p
kernel32.GlobalUnlock.argtypes = [ctypes.c_void_p]
kernel32.GlobalSize.argtypes = [ctypes.c_void_p]
CF_DIB = 8; GMEM_MOVEABLE = 0x0002

# --- Physics / Math (Logic UNCHANGED) ---
def lorentzian(x, amp, cen, wid):
    return amp * (wid**2) / ((x - cen)**2 + wid**2)

def multi_lorentzian(x, *params):
    y = np.zeros_like(x)
    for i in range(0, len(params), 3):
        y += lorentzian(x, params[i], params[i+1], params[i+2])
    return y

def get_ir_assignment_data(wn):
    wn = float(wn)
    if 3600 <= wn <= 3700: return "O-H $_{free}$", r"$\nu$"
    elif 3200 <= wn < 3600: return "O-H $_{H-bond}$", r"$\nu$"
    elif 3300 <= wn < 3500: return "N-H", r"$\nu$"
    elif 3010 <= wn < 3100: return "=C-H $_{sp2}$", r"$\nu$"
    elif 2850 <= wn < 3000: return "C-H $_{sp3}$", r"$\nu$"
    elif 2700 <= wn < 2850: return "C-H $_{Ald}$", r"$\nu$"
    elif 2500 <= wn < 2700: return "S-H/COOH", r"$\nu$"
    elif 2200 <= wn < 2260: return "C≡N", r"$\nu$"
    elif 2100 <= wn < 2200: return "C≡C", r"$\nu$"
    elif 1750 <= wn < 1780: return "C=O $_{Ester}$", r"$\nu$"
    elif 1735 <= wn < 1750: return "C=O $_{Est/Ald}$", r"$\nu$"
    elif 1700 <= wn < 1735: return "C=O $_{Ketone}$", r"$\nu$"
    elif 1680 <= wn < 1700: return "C=O $_{Amide}$", r"$\nu$"
    elif 1630 <= wn < 1680: return "C=C $_{Alkene}$", r"$\nu$"
    elif 1600 <= wn < 1630: return "C=C $_{Arom}$", r"$\nu$"
    elif 1500 <= wn < 1600: return "N-H/C=C", r"$\delta$"
    elif 1450 <= wn < 1480: return "C-H $_{CH2/3}$", r"$\delta$"
    elif 1370 <= wn < 1400: return "C-H $_{CH3}$", r"$\delta$"
    elif 1000 <= wn < 1300: return "C-O/C-N", r"$\nu$"
    elif 675 <= wn < 1000:  return "=C-H $_{oop}$", r"$\gamma$"
    elif 600 <= wn < 675:   return "Fingerprint", ""
    else: return "Peak", ""

def get_full_assignment(wn):
    group, sym = get_ir_assignment_data(wn)
    if group == "Peak": return "Unknown"
    return f"{group} ({sym})".strip()

def get_short_label(wn):
    group, sym = get_ir_assignment_data(wn)
    if group == "Peak": return f"{wn:.0f}"
    return f"{wn:.0f} ({sym} {group})"

class IRDeconvolutionApp:
    def __init__(self, root):
        self.root = root
        self.root.title("AjTeeranan IR Peak Analyzer V.2.01.Y2026")
        
        # --- 1. STARTUP SEQUENCE ---
        self.root.update_idletasks()
        screen_w = self.root.winfo_screenwidth()
        screen_h = self.root.winfo_screenheight()
        target_w = int(screen_w * 0.75)
        target_h = int(screen_h * 0.75)
        pos_x = (screen_w - target_w) // 2
        pos_y = (screen_h - target_h) // 2
        self.geometry_75 = f"{target_w}x{target_h}+{pos_x}+{pos_y}"
        self.root.geometry(self.geometry_75)
        
        def perform_startup_dance():
            self.root.state('zoomed')
            self.root.update()
            self.root.after(300, lambda: self.root.state('normal'))
        self.root.after(200, perform_startup_dance)

        # --- DESIGN SYSTEM (MATERIAL DESIGN) ---
        self.FONT_MAIN = ("Segoe UI", 10)
        self.FONT_BOLD = ("Segoe UI", 10, "bold")
        self.FONT_HEADER = ("Segoe UI", 11, "bold")
        self.FONT_TITLE = ("Segoe UI Emoji", 14, "bold")
        
        # Color Palette
        self.COL_BG_MAIN = "#FAFAFA"
        self.COL_HEADER_BG = "#FFECB3" # Yellow for Header
        
        self.COL_SECT_1 = "#E3F2FD" # Blue 50
        self.COL_BTN_1  = "#1976D2" # Blue 700
        self.COL_SECT_2 = "#E0F2F1" # Teal 50
        self.COL_BTN_2  = "#00796B" # Teal 700
        self.COL_SECT_3 = "#FFF3E0" # Orange 50
        self.COL_BTN_3  = "#F57C00" # Orange 700
        self.COL_SECT_4 = "#F3E5F5" # Purple 50
        self.COL_BTN_4  = "#7B1FA2" # Purple 700
        self.COL_SECT_R = "#FFEBEE" # Red 50
        self.COL_BTN_R  = "#D32F2F" # Red 700
        self.COL_TEXT   = "#37474F" # Blue Grey 800

        self.root.configure(bg=self.COL_BG_MAIN)
        self.root.option_add("*Font", self.FONT_MAIN)
        self.root.option_add("*Entry.relief", "solid")
        self.root.option_add("*Entry.bd", 1)

        # Config ttk styles
        style = ttk.Style()
        style.theme_use('clam')
        style.configure("Treeview", font=("Segoe UI", 10), rowheight=28, background="white", bordercolor="#EEEEEE")
        style.configure("Treeview.Heading", font=("Segoe UI", 10, "bold"), background="#EEEEEE", foreground="#333333", relief="flat")
        style.map("Treeview.Heading", background=[('active', '#E0E0E0')])

        # Matplotlib
        plt.rcParams.update({
            'font.family': 'sans-serif', 'font.sans-serif': ['Segoe UI', 'Arial'],
            'font.size': 12, 'figure.facecolor': 'white', 
            'axes.titlesize': 14, 'axes.labelsize': 14, 
            'xtick.labelsize': 11, 'ytick.labelsize': 11,
            'mathtext.fontset': 'cm'
        })

        # --- DATA STATE ---
        self.x_raw = None; self.y_raw = None     
        self.x_data = None; self.y_data = None
        self.y_abs_calc = None 
        self.is_absorbance = False 
        
        self.manual_peaks = []      
        self.excluded_peaks = []    
        self.detected_peaks = []    
        self.initial_params = []  
        self.fitted_params = []   
        
        self.show_labels_var = tk.BooleanVar(value=True)
        self.snap_to_max_var = tk.BooleanVar(value=False)
        self.label_jitter = 0
        
        # ** DEFAULTS **
        self.graph_font_size = tk.IntVar(value=14)
        self.label_font_size = tk.IntVar(value=11)
        self.label_spacing = tk.DoubleVar(value=0.015)
        self.var_leg_ratio = tk.DoubleVar(value=0.65)
        self.var_text_ratio = tk.DoubleVar(value=0.75)
        self.min_height = tk.DoubleVar(value=0.001)
        self.prominence = tk.DoubleVar(value=0.005)

        # ================= UI CONSTRUCTION =================
        
        # 1. HEADER (Yellow)
        header_frame = tk.Frame(self.root, bg=self.COL_HEADER_BG, pady=8, padx=20)
        header_frame.pack(side=tk.TOP, fill=tk.X)
        tk.Label(header_frame, text="AjTeeranan IR Peak Analyzer V.2.01.Y2026", 
                 font=self.FONT_TITLE, fg="#D84315", bg=self.COL_HEADER_BG).pack(side=tk.LEFT)
        
        # 2. CONTROL RIBBON
        ribbon_frame = tk.Frame(self.root, bg=self.COL_BG_MAIN)
        ribbon_frame.pack(side=tk.TOP, fill=tk.X, padx=5, pady=5)

        # --- SECT 1: DATA & AXIS (Blue) ---
        f1 = self.create_card(ribbon_frame, "1. DATA & AXIS", self.COL_SECT_1, self.COL_BTN_1)
        f1.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=2) 
        
        r1_1 = tk.Frame(f1, bg=self.COL_SECT_1); r1_1.pack(fill=tk.X, pady=1)
        self.mk_flat_btn(r1_1, "PASTE", self.COL_BTN_1, lambda: self.paste_data())
        self.mk_flat_btn(r1_1, "%T ➔ ABS", self.COL_BTN_1, self.convert_to_absorbance)
        self.mk_flat_btn(r1_1, "BASE=0", self.COL_BTN_1, self.baseline_correction)
        self.mk_flat_btn(r1_1, "CLEAR", self.COL_BTN_R, self.clear_input_data)

        r1_2 = tk.Frame(f1, bg=self.COL_SECT_1); r1_2.pack(fill=tk.X, pady=2)
        tk.Label(r1_2, text="X:", bg=self.COL_SECT_1, font=self.FONT_BOLD).pack(side=tk.LEFT)
        self.var_auto_x = tk.BooleanVar(value=True)
        tk.Checkbutton(r1_2, text="AUTO", variable=self.var_auto_x, command=self.toggle_x_range, bg=self.COL_SECT_1, activebackground=self.COL_SECT_1).pack(side=tk.LEFT)
        self.var_min_wn = tk.StringVar(value="Auto"); self.var_max_wn = tk.StringVar(value="Auto")
        self.entry_x1 = tk.Entry(r1_2, textvariable=self.var_min_wn, width=5, justify='center', state='disabled'); self.entry_x1.pack(side=tk.LEFT, padx=1)
        tk.Label(r1_2, text="-", bg=self.COL_SECT_1).pack(side=tk.LEFT)
        self.entry_x2 = tk.Entry(r1_2, textvariable=self.var_max_wn, width=5, justify='center', state='disabled'); self.entry_x2.pack(side=tk.LEFT, padx=1)
        self.mk_mini_btn(r1_2, "SET", self.COL_BTN_1, self.apply_range_filter)

        r1_3 = tk.Frame(f1, bg=self.COL_SECT_1); r1_3.pack(fill=tk.X, pady=1)
        tk.Label(r1_3, text="Y:", bg=self.COL_SECT_1, font=self.FONT_BOLD).pack(side=tk.LEFT)
        self.var_auto_y = tk.BooleanVar(value=True)
        tk.Checkbutton(r1_3, text="AUTO", variable=self.var_auto_y, command=self.toggle_y_range, bg=self.COL_SECT_1, activebackground=self.COL_SECT_1).pack(side=tk.LEFT)
        self.var_min_y = tk.StringVar(value="Auto"); self.var_max_y = tk.StringVar(value="Auto")
        self.entry_y1 = tk.Entry(r1_3, textvariable=self.var_min_y, width=5, justify='center', state='disabled'); self.entry_y1.pack(side=tk.LEFT, padx=1)
        tk.Label(r1_3, text="-", bg=self.COL_SECT_1).pack(side=tk.LEFT)
        self.entry_y2 = tk.Entry(r1_3, textvariable=self.var_max_y, width=5, justify='center', state='disabled'); self.entry_y2.pack(side=tk.LEFT, padx=1)
        self.mk_mini_btn(r1_3, "SET", self.COL_BTN_1, self.apply_y_range)

        # --- SECT 2: VISUAL CONTROL (Teal) ---
        f2 = self.create_card(ribbon_frame, "2. VISUAL CONTROL", self.COL_SECT_2, self.COL_BTN_2)
        f2.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=2)
        
        r2_1 = tk.Frame(f2, bg=self.COL_SECT_2); r2_1.pack(fill=tk.X, pady=1)
        tk.Label(r2_1, text="PLOT FONT:", bg=self.COL_SECT_2, font=self.FONT_BOLD).pack(side=tk.LEFT)
        self.mk_tuner(r2_1, self.graph_font_size, 1, 1, self.COL_BTN_2, self.adjust_font)
        tk.Label(r2_1, text="PEAK LABEL:", bg=self.COL_SECT_2, font=self.FONT_BOLD).pack(side=tk.LEFT, padx=(5,0))
        self.mk_tuner(r2_1, self.label_font_size, 1, 1, self.COL_BTN_2, self.adjust_font)

        r2_3 = tk.Frame(f2, bg=self.COL_SECT_2); r2_3.pack(fill=tk.X, pady=5)
        self.create_precision_adjuster(r2_3, "PEAK LABEL SPACE:", self.label_spacing, 0.001, 0.005, self.COL_SECT_2, 
                                       cmd=lambda: self.plot_current_state(3), width=20)
        
        r2_4 = tk.Frame(f2, bg=self.COL_SECT_2); r2_4.pack(fill=tk.X, pady=5)
        self.create_precision_adjuster(r2_4, "PEAK LABEL LEG:", self.var_leg_ratio, 0.01, 0.05, self.COL_SECT_2, 
                                       cmd=lambda: self.plot_current_state(3), width=20)
        
        r2_5 = tk.Frame(f2, bg=self.COL_SECT_2); r2_5.pack(fill=tk.X, pady=5)
        self.create_precision_adjuster(r2_5, "PEAK LABEL TEXT:", self.var_text_ratio, 0.01, 0.05, self.COL_SECT_2, 
                                       cmd=lambda: self.plot_current_state(3), width=20)

        # --- SECT 3: PEAK DETECTION (Orange) ---
        f3 = self.create_card(ribbon_frame, "3. PEAK DETECTION", self.COL_SECT_3, self.COL_BTN_3)
        f3.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=2)
        
        r3_1 = tk.Frame(f3, bg=self.COL_SECT_3); r3_1.pack(fill=tk.X, pady=5)
        self.create_precision_adjuster(r3_1, "MIN HEIGHT", self.min_height, 0.001, 0.005, self.COL_SECT_3, 
                                       cmd=self.step1_detect_peaks, width=20)
        
        r3_2 = tk.Frame(f3, bg=self.COL_SECT_3); r3_2.pack(fill=tk.X, pady=5)
        self.create_precision_adjuster(r3_2, "PROMINENCE", self.prominence, 0.001, 0.005, self.COL_SECT_3, 
                                       cmd=self.step1_detect_peaks, width=20)
        
        r3_3 = tk.Frame(f3, bg=self.COL_SECT_3); r3_3.pack(fill=tk.X, pady=5)
        self.mk_flat_btn(r3_3, "AUTO DETECT", self.COL_BTN_1, self.step1_detect_peaks)
        self.mk_flat_btn(r3_3, "RESET", self.COL_BTN_R, self.clear_manual)
        tk.Checkbutton(r3_3, text="SNAP", variable=self.snap_to_max_var, bg=self.COL_SECT_3, activebackground=self.COL_SECT_3).pack(side=tk.LEFT, padx=5)

        # --- SECT 4: MODEL & FIT (Purple) ---
        f4 = self.create_card(ribbon_frame, "4. MODEL & LORENTZIAN FIT", self.COL_SECT_4, self.COL_BTN_4)
        f4.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=2)
        
        # Row 4.1: Initial Model
        r4_1 = tk.Frame(f4, bg=self.COL_SECT_4)
        r4_1.pack(fill=tk.X, pady=3)
        tk.Label(r4_1, text="INITIAL MODEL:", bg=self.COL_SECT_4, font=("Segoe UI", 9, "bold"), fg="#666").pack(side=tk.LEFT)
        self.mk_flat_btn(r4_1, "GENERATE MODEL", self.COL_BTN_4, self.step2_initial_guess, side=tk.RIGHT)
        
        # Row 4.2: Optimization
        r4_2 = tk.Frame(f4, bg=self.COL_SECT_4)
        r4_2.pack(fill=tk.X, pady=3)
        tk.Label(r4_2, text="OPTIMIZATION:", bg=self.COL_SECT_4, font=("Segoe UI", 9, "bold"), fg="#666").pack(side=tk.LEFT)
        self.mk_flat_btn(r4_2, "START FITTING", "#2E7D32", self.step3_optimize, side=tk.RIGHT)
        
        # Row 4.3: Status
        self.fit_stats_var = tk.StringVar(value="STATUS: READY"); 
        tk.Label(f4, textvariable=self.fit_stats_var, fg="#2E7D32", bg=self.COL_SECT_4, font=("Segoe UI", 9, "bold")).pack(pady=5)

        # --- RESULTS BAR ---
        bottom_frame = tk.Frame(self.root, bg=self.COL_SECT_R, bd=0)
        bottom_frame.pack(side=tk.BOTTOM, fill=tk.X)
        b_head = tk.Frame(bottom_frame, bg=self.COL_SECT_R, padx=10, pady=5)
        b_head.pack(fill=tk.X)
        tk.Label(b_head, text="6. ANALYSIS RESULTS TABLE", font=self.FONT_HEADER, bg=self.COL_SECT_R, fg=self.COL_BTN_R).pack(side=tk.LEFT)
        self.mk_flat_btn(b_head, "EXIT APP", self.COL_BTN_R, self.root.quit, side=tk.RIGHT)
        self.mk_flat_btn(b_head, "COPY RESULTS TABLE", self.COL_BTN_R, self.copy_results_to_clipboard, side=tk.RIGHT)

        self.tree_scroll = ttk.Scrollbar(bottom_frame)
        self.tree_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.tree = ttk.Treeview(bottom_frame, columns=("wn", "assign", "amp", "width", "area"), 
                                 show="headings", height=6, yscrollcommand=self.tree_scroll.set)
        self.tree_scroll.config(command=self.tree.yview)
        cols = [("wn", "Position (cm⁻¹)"), ("assign", "Assignment"), ("amp", "Height"), ("width", "Width"), ("area", "Area")]
        for id, txt in cols: self.tree.heading(id, text=txt); self.tree.column(id, anchor=tk.CENTER)
        self.tree.column("wn", width=150); self.tree.column("assign", width=400)
        self.tree.pack(side=tk.LEFT, fill=tk.X, expand=True)

        # --- MAIN CONTENT ---
        main_content = tk.Frame(self.root, bg=self.COL_BG_MAIN)
        main_content.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=10, pady=5)

        # LEFT LISTS (COLORED)
        left_col = tk.Frame(main_content, bg=self.COL_BG_MAIN, width=320)
        left_col.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 10))
        
        # Table 1: Input (Blue)
        tk.Label(left_col, text="INPUT DATA LIST", font=self.FONT_HEADER, bg=self.COL_BG_MAIN, fg=self.COL_BTN_1).pack(anchor='w')
        self.input_tree = self.create_colored_table(left_col, "input_tree", ["cm⁻¹", "%T", "Abs"], 8, "blue")
        
        # Table 2: Peak (Orange)
        tk.Label(left_col, text="DETECTED PEAKS", font=self.FONT_HEADER, bg=self.COL_BG_MAIN, fg=self.COL_BTN_3).pack(anchor='w', pady=(10,0))
        self.peak_list = self.create_colored_table(left_col, "peak_list", ["Peak", "Int"], 8, "orange")
        self.mk_flat_btn(left_col, "DELETE PEAK", self.COL_BTN_R, self.delete_selected_peak_from_list, fill=tk.X)

        # RIGHT GRAPH
        right_col = tk.Frame(main_content, bg="white", bd=1, relief="solid")
        right_col.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        g_toolbar = tk.Frame(right_col, bg="white", padx=5, pady=5)
        g_toolbar.pack(fill=tk.X)
        tk.Label(g_toolbar, text="5. VISUALIZATION GRAPH", font=self.FONT_HEADER, bg="white", fg=self.COL_TEXT).pack(side=tk.LEFT)
        self.mk_mini_btn(g_toolbar, "COPY IMG TO CLIPBOARD", "#455A64", self.copy_graph_clipboard, side=tk.RIGHT)
        self.mk_mini_btn(g_toolbar, "SAVE IMG TO PNG FILE", "#455A64", self.save_graph_png, side=tk.RIGHT)
        tk.Checkbutton(g_toolbar, text="SHOW LABELS", variable=self.show_labels_var, command=lambda: self.plot_current_state(3), bg="white", font=("Segoe UI", 10, "bold")).pack(side=tk.RIGHT, padx=10)

        self.fig = Figure(figsize=(6, 4.5), dpi=100, layout='constrained')
        self.ax = self.fig.add_subplot(111)
        self.canvas = FigureCanvasTkAgg(self.fig, master=right_col)
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self.canvas.mpl_connect('button_press_event', self.on_click)

        self.root.bind("<Control-v>", self.paste_data)

    # --- COLORED TABLE HELPER ---
    def create_colored_table(self, parent, attr_name, headers, height, color_theme):
        f = tk.Frame(parent, bg=self.COL_BG_MAIN); f.pack(fill=tk.BOTH, expand=True, pady=(0,5))
        s = ttk.Scrollbar(f); s.pack(side=tk.RIGHT, fill=tk.Y)
        cols = tuple(f"c{i}" for i in range(len(headers)))
        
        # Configure Styles based on theme
        style_name = f"{attr_name}.Treeview"
        style = ttk.Style()
        
        if color_theme == "blue":
            head_bg = self.COL_SECT_1; head_fg = self.COL_BTN_1
            stripe_bg = "#F5FBFD" # Very light blue
        else: # orange
            head_bg = self.COL_SECT_3; head_fg = self.COL_BTN_3
            stripe_bg = "#FEF8F3" # Very light orange

        style.configure(style_name, font=("Segoe UI", 10), rowheight=26)
        style.configure(style_name + ".Heading", background=head_bg, foreground=head_fg, font=("Segoe UI", 9, "bold"))
        
        tv = ttk.Treeview(f, columns=cols, show="headings", height=height, yscrollcommand=s.set, style=style_name)
        s.config(command=tv.yview)
        
        for i, h in enumerate(headers):
            tv.heading(f"c{i}", text=h)
            tv.column(f"c{i}", width=90, anchor='center')
        
        tv.tag_configure('oddrow', background=stripe_bg)
        tv.tag_configure('evenrow', background="white")
        
        tv.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        setattr(self, attr_name, tv)
        return tv

    # --- UI HELPERS ---
    def create_card(self, parent, title, bg_color, title_color):
        f = tk.Frame(parent, bg=bg_color, padx=5, pady=5, relief="flat")
        tk.Label(f, text=title, font=("Segoe UI", 10, "bold"), bg=bg_color, fg=title_color).pack(anchor='nw', pady=(0, 5))
        return f

    def mk_flat_btn(self, parent, text, color, cmd, side=tk.LEFT, fill=None, expand=False, pad=(2,2)):
        btn = tk.Button(parent, text=text, bg=color, fg="white", activebackground="white", activeforeground=color,
                        command=cmd, font=("Segoe UI", 9, "bold"), relief="flat", overrelief="raised", padx=10, pady=2, cursor="hand2")
        btn.pack(side=side, fill=fill, expand=expand, padx=pad[0], pady=pad[1])
        return btn

    def mk_mini_btn(self, parent, text, color, cmd, side=tk.LEFT, w=None, pad=(1,1)):
        btn = tk.Button(parent, text=text, bg=color, fg="white", activebackground="white", activeforeground=color,
                        command=cmd, font=("Segoe UI", 8, "bold"), relief="flat", overrelief="raised", padx=5, pady=0, cursor="hand2")
        if w: btn.config(width=w)
        btn.pack(side=side, padx=pad[0], pady=pad[1])
        return btn

    def mk_tuner(self, parent, var, fine, coarse, color, cmd_func):
        self.mk_mini_btn(parent, "-", "#90A4AE", lambda: cmd_func(var, -1), w=2)
        tk.Label(parent, textvariable=var, width=3, bg="white", relief="solid", bd=1).pack(side=tk.LEFT, padx=2)
        self.mk_mini_btn(parent, "+", "#90A4AE", lambda: cmd_func(var, 1), w=2)

    def create_precision_adjuster(self, parent, label, var, fine_step, coarse_step, bg_color, cmd=None, side_pad=(0,0), width=None):
        f = tk.Frame(parent, bg=bg_color); f.pack(side=tk.LEFT, padx=side_pad, pady=1)
        lbl_w = width if width else (len(label) if len(label) > 6 else 10)
        tk.Label(f, text=label, width=lbl_w, bg=bg_color, font=("Segoe UI", 9), anchor='w').pack(side=tk.LEFT)
        def update(delta):
            new_val = var.get() + delta
            if var == self.label_spacing: new_val = max(0.001, new_val)
            elif var == self.min_height or var == self.prominence: new_val = max(0.001, new_val)
            elif var == self.var_leg_ratio or var == self.var_text_ratio: new_val = min(0.98, max(0.1, new_val))
            var.set(round(new_val, 4))
            if cmd: cmd()
        self.mk_mini_btn(f, "<<", "#546E7A", lambda: update(-coarse_step), w=2)
        self.mk_mini_btn(f, "<", "#90A4AE", lambda: update(-fine_step), w=2)
        tk.Label(f, textvariable=var, width=6, bg="white", relief="solid", bd=1, font=("Segoe UI", 9)).pack(side=tk.LEFT, padx=1)
        self.mk_mini_btn(f, ">", "#90A4AE", lambda: update(fine_step), w=2)
        self.mk_mini_btn(f, ">>", "#546E7A", lambda: update(coarse_step), w=2)

    # --- LOGIC FUNCTIONS (UNCHANGED) ---
    def adjust_font(self, var, delta):
        new_size = max(6, var.get() + delta)
        var.set(new_size)
        self.plot_current_state(3)

    def toggle_x_range(self): 
        st = 'disabled' if self.var_auto_x.get() else 'normal'
        self.entry_x1.config(state=st); self.entry_x2.config(state=st)
        if self.var_auto_x.get(): self.apply_range_filter()
    def toggle_y_range(self):
        st = 'disabled' if self.var_auto_y.get() else 'normal'
        self.entry_y1.config(state=st); self.entry_y2.config(state=st)
        if self.var_auto_y.get(): self.apply_y_range()

    def paste_data(self, event=None):
        try:
            self.root.update()
            try: clipboard = self.root.clipboard_get()
            except: raise ValueError("Empty")
            rows = clipboard.strip().split('\n')
            wn_list = []; int_list = []
            for row in rows:
                p = row.replace('\t', ' ').split()
                if len(p) >= 2: 
                    try: wn_list.append(float(p[0])); int_list.append(float(p[1]))
                    except: continue
            if not wn_list: return
            x_arr = np.array(wn_list); y_arr = np.array(int_list)
            idx = np.argsort(x_arr)
            self.x_raw = x_arr[idx]; self.y_raw = y_arr[idx]
            self.y_abs_calc = None 
            self.is_absorbance = False
            self.x_data = self.x_raw.copy(); self.y_data = self.y_raw.copy()
            self.var_auto_x.set(True); self.toggle_x_range()
            self.var_auto_y.set(True); self.toggle_y_range()
            self.var_min_wn.set("Auto"); self.var_max_wn.set("Auto")
            self.var_min_y.set("Auto"); self.var_max_y.set("Auto")
            self.update_input_tree()
            self.step1_detect_peaks()
        except Exception as e: messagebox.showerror("Paste Error", str(e))

    def convert_to_absorbance(self):
        if self.y_raw is None: return
        try:
            y_safe = np.where(self.y_raw <= 0, 0.0001, self.y_raw)
            self.y_abs_calc = 2 - np.log10(y_safe)
            self.y_data = self.y_abs_calc.copy()
            self.is_absorbance = True
            self.var_auto_y.set(False)
            self.var_min_y.set("0"); self.var_max_y.set("0.7")
            self.toggle_y_range()
            self.update_input_tree()
            self.apply_range_filter()
        except: pass

    def baseline_correction(self):
        if self.y_data is None: return
        self.y_data = self.y_data - np.min(self.y_data)
        self.apply_range_filter()

    def clear_input_data(self):
        self.x_raw = None; self.y_raw = None; self.x_data = None; self.y_data = None; self.y_abs_calc = None
        self.input_tree.delete(*self.input_tree.get_children())
        self.peak_list.delete(*self.peak_list.get_children())
        self.tree.delete(*self.tree.get_children())
        self.ax.clear(); self.canvas.draw()
        self.manual_peaks = []; self.excluded_peaks = []; self.detected_peaks = []
        self.initial_params = []; self.fitted_params = []; self.fit_stats_var.set("Ready")
        self.var_auto_x.set(True); self.toggle_x_range()
        self.var_auto_y.set(True); self.toggle_y_range()

    def apply_range_filter(self):
        if self.x_raw is None: return
        try:
            if self.var_auto_x.get():
                self.x_data = self.x_raw.copy()
                if self.is_absorbance: self.y_data = self.y_abs_calc.copy()
                else: self.y_data = self.y_raw.copy()
                self.var_min_wn.set(f"{int(self.x_raw.max())}"); self.var_max_wn.set(f"{int(self.x_raw.min())}")
            else:
                val1 = float(self.var_min_wn.get()); val2 = float(self.var_max_wn.get())
                w_min = min(val1, val2); w_max = max(val1, val2)
                mask = (self.x_raw >= w_min) & (self.x_raw <= w_max)
                self.x_data = self.x_raw[mask]
                if self.is_absorbance: self.y_data = self.y_abs_calc[mask]
                else: self.y_data = self.y_raw[mask]
            if len(self.x_data) == 0: return
            self.step1_detect_peaks()
        except: pass

    def apply_y_range(self): self.plot_current_state(3)

    def update_input_tree(self):
        self.input_tree.delete(*self.input_tree.get_children())
        if self.x_raw is not None:
            step = 1 if len(self.x_raw) < 2000 else len(self.x_raw)//1000
            for i in range(0, len(self.x_raw), step):
                w = f"{self.x_raw[i]:.2f}"; t = f"{self.y_raw[i]:.2f}"
                a = f"{self.y_abs_calc[i]:.3f}" if self.y_abs_calc is not None else "-"
                tag = 'oddrow' if (i//step)%2==1 else 'evenrow'
                self.input_tree.insert("", tk.END, values=(w, t, a), tags=(tag,))

    def update_peak_list_box(self):
        self.peak_list.delete(*self.peak_list.get_children())
        if self.x_data is None: return
        for i, p in enumerate(self.detected_peaks):
            idx = (np.abs(self.x_data - p)).argmin()
            inten = self.y_data[idx]
            tag = 'oddrow' if i%2==1 else 'evenrow'
            self.peak_list.insert("", tk.END, values=(f"{p:.2f}", f"{inten:.3f}"), tags=(tag,))

    def delete_selected_peak_from_list(self):
        selected = self.peak_list.selection()
        for item in selected:
            vals = self.peak_list.item(item)['values']
            self.perform_delete(float(vals[0]))
        self.step1_detect_peaks()

    def perform_delete(self, wn):
        found_manual = False
        if self.manual_peaks:
            dist = [abs(p - wn) for p in self.manual_peaks]
            if min(dist) < 10:
                target = self.manual_peaks[dist.index(min(dist))]
                self.manual_peaks.remove(target); found_manual = True
        if not found_manual: self.excluded_peaks.append(wn)

    def on_click(self, event):
        if len(self.fitted_params) > 0: return 
        if event.inaxes != self.ax: return
        if event.button == 1: 
            x_click = event.xdata
            if self.snap_to_max_var.get() and self.x_data is not None:
                idx_nearest = (np.abs(self.x_data - x_click)).argmin()
                window = 20
                start = max(0, idx_nearest - window)
                end = min(len(self.y_data), idx_nearest + window)
                if start < end:
                    local_max_idx = start + np.argmax(self.y_data[start:end])
                    self.manual_peaks.append(self.x_data[local_max_idx])
                else: self.manual_peaks.append(x_click)
            else: self.manual_peaks.append(x_click)
        elif event.button == 3: self.perform_delete(event.xdata)
        self.step1_detect_peaks()

    def clear_manual(self):
        self.manual_peaks = []; self.excluded_peaks = []; self.fitted_params = []
        self.step1_detect_peaks()

    def step1_detect_peaks(self):
        if self.x_data is None: return
        auto_idxs, _ = find_peaks(self.y_data, height=self.min_height.get(), prominence=self.prominence.get())
        auto_peaks = list(self.x_data[auto_idxs])
        valid_auto = []
        for ap in auto_peaks:
            is_excluded = False
            for ex in self.excluded_peaks:
                if abs(ap - ex) < 10.0: is_excluded = True; break
            if not is_excluded: valid_auto.append(ap)
        self.detected_peaks = sorted(list(set(valid_auto + self.manual_peaks)))
        self.update_peak_list_box()
        self.plot_current_state(stage=1)

    def step2_initial_guess(self):
        if not self.detected_peaks: return
        self.initial_params = []
        for cen in self.detected_peaks:
            if cen < self.x_data.min() or cen > self.x_data.max(): continue
            idx = (np.abs(self.x_data - cen)).argmin()
            self.initial_params.extend([self.y_data[idx], self.x_data[idx], 10.0])
        self.plot_current_state(stage=2)

    def step3_optimize(self):
        if not self.initial_params: return
        try:
            popt, _ = curve_fit(multi_lorentzian, self.x_data, self.y_data, p0=self.initial_params, maxfev=15000)
            self.fitted_params = popt
            y_fit = multi_lorentzian(self.x_data, *popt)
            res = self.y_data - y_fit
            rss = np.sum(res**2); ss_tot = np.sum((self.y_data - np.mean(self.y_data))**2)
            r2 = 1 - (rss/ss_tot)
            self.fit_stats_var.set(f"GOODNESS OF FITTING: R² = {r2:.4f}")
            self.tree.delete(*self.tree.get_children())
            for i in range(0, len(popt), 3):
                amp, cen, wid = popt[i], popt[i+1], abs(popt[i+2])
                area = amp * wid * np.pi
                self.tree.insert("", tk.END, values=(f"{cen:.1f}", get_full_assignment(cen), f"{amp:.3f}", f"{wid:.3f}", f"{area:.3f}"))
            self.plot_current_state(stage=3)
        except Exception as e: messagebox.showerror("Error", str(e))

    def realign_labels(self):
        self.label_jitter = random.uniform(0, 100)
        self.plot_current_state(3)

    def plot_current_state(self, stage=1):
        self.ax.clear()
        fs_graph = self.graph_font_size.get()
        fs_label = self.label_font_size.get()
        space_val = self.label_spacing.get()
        knee_r = self.var_leg_ratio.get()
        text_r = self.var_text_ratio.get()
        
        self.ax.tick_params(axis='both', which='major', labelsize=fs_graph)
        self.ax.set_xlabel("Wavenumber (cm⁻¹)", fontsize=fs_graph)
        self.ax.set_ylabel("Absorbance" if self.is_absorbance else "Intensity", fontsize=fs_graph)
        
        if self.x_data is None: self.canvas.draw(); return
        
        self.ax.plot(self.x_data, self.y_data, 'k', alpha=0.8, label='Data', lw=2.0)

        if not self.var_auto_x.get():
            try:
                x1 = float(self.var_min_wn.get()); x2 = float(self.var_max_wn.get())
                self.ax.set_xlim(max(x1, x2), min(x1, x2))
            except: pass
        else: self.ax.set_xlim(self.x_data.max(), self.x_data.min())

        self.ax.autoscale(enable=True, axis='y')
        ymin, ymax_data = self.ax.get_ylim()
        range_y = ymax_data - ymin
        fixed_ymax = ymin + (range_y / knee_r)

        if not self.var_auto_y.get():
            try:
                y1 = float(self.var_min_y.get()); y2 = float(self.var_max_y.get())
                self.ax.set_ylim(bottom=y1, top=y2)
                ymin, fixed_ymax = y1, y2
                range_y = fixed_ymax - ymin
            except: pass
        else:
            self.ax.set_ylim(bottom=ymin, top=fixed_ymax)

        if stage == 1:
            for p in self.detected_peaks: 
                if self.x_data.min() <= p <= self.x_data.max():
                    self.ax.plot(p, np.interp(p, self.x_data, self.y_data), "bx", ms=10)
        elif stage == 2:
            if self.initial_params:
                self.ax.plot(self.x_data, multi_lorentzian(self.x_data, *self.initial_params), 'g--', label='Guess', lw=2)
        elif stage == 3:
            if len(self.fitted_params) > 0:
                y_fit_total = multi_lorentzian(self.x_data, *self.fitted_params)
                self.ax.plot(self.x_data, y_fit_total, 'r-', label='Fit', lw=2.0)
                
                xlim = self.ax.get_xlim(); view_max, view_min = max(xlim), min(xlim)
                visible_peaks = []
                peak_colors = plt.cm.nipy_spectral(np.linspace(0, 0.9, len(self.fitted_params)//3))
                
                for i in range(0, len(self.fitted_params), 3):
                    amp, cen, wid = self.fitted_params[i:i+3]
                    p_data = {'cen': cen, 'amp': amp, 'wid': wid, 'color': peak_colors[i//3]}
                    if view_min <= cen <= view_max:
                        idx = (np.abs(self.x_data - cen)).argmin()
                        p_data['y_peak'] = y_fit_total[idx]
                        p_data['text'] = get_short_label(cen)
                        visible_peaks.append(p_data)
                    self.ax.fill_between(self.x_data, lorentzian(self.x_data, amp, cen, wid), alpha=0.3, color=p_data['color'])

                if self.show_labels_var.get():
                    visible_peaks.sort(key=lambda x: x['cen'])
                    curr_ymin, curr_ymax = self.ax.get_ylim()
                    total_view_h = curr_ymax - curr_ymin
                    knee_y_base = curr_ymin + (total_view_h * knee_r)
                    text_y_base = curr_ymin + (total_view_h * text_r)
                    spacing_offset = total_view_h * 0.005 

                    min_dist = (view_max - view_min) * space_val
                    for p in visible_peaks: p['x_text'] = p['cen']
                    for _ in range(5):
                        for i in range(len(visible_peaks)-1):
                            curr = visible_peaks[i]['x_text']
                            next_val = visible_peaks[i+1]['x_text']
                            if next_val < curr + min_dist:
                                visible_peaks[i+1]['x_text'] = curr + min_dist
                                
                    for i, p in enumerate(visible_peaks):
                        x_peak = p['cen']; y_peak = p['y_peak']; x_text = p['x_text']
                        knee_y = knee_y_base + (i%3)*(total_view_h * 0.02)
                        line_end_y = text_y_base
                        text_draw_y = text_y_base + spacing_offset
                        
                        c = p['color']
                        self.ax.plot([x_peak, x_peak], [y_peak, knee_y], color=c, lw=1.0, alpha=0.9)
                        self.ax.plot([x_peak, x_text], [knee_y, knee_y], color=c, lw=1.0, alpha=0.9)
                        self.ax.plot([x_text, x_text], [knee_y, line_end_y], color=c, lw=1.0, alpha=0.9)
                        self.ax.text(x_text, text_draw_y, p['text'], color='black', fontsize=fs_label, 
                                     ha='center', va='bottom', rotation=90, fontweight='normal')
                    
                    if self.var_auto_x.get() and visible_peaks:
                        mx = max(p['x_text'] for p in visible_peaks)
                        cur_max = self.ax.get_xlim()[0]
                        if mx > cur_max: self.ax.set_xlim(left=mx + min_dist)

        self.canvas.draw()

    def copy_results_to_clipboard(self):
        if not self.tree.get_children(): return
        headers = ["Wavenumber", "Assignment", "Height", "Width", "Area"]
        data_str = "\t".join(headers) + "\n"
        for item in self.tree.get_children():
            data_str += "\t".join([str(r) for r in self.tree.item(item)['values']]) + "\n"
        self.root.clipboard_clear(); self.root.clipboard_append(data_str)
        messagebox.showinfo("Success", "Table Copied!")

    def save_graph_png(self):
        f = filedialog.asksaveasfilename(defaultextension=".png", filetypes=[("PNG", "*.png")])
        if f: self.fig.savefig(f, dpi=300, bbox_inches='tight')

    def copy_graph_clipboard(self):
        try:
            buf = BytesIO(); self.fig.savefig(buf, format='png', dpi=300, bbox_inches='tight')
            buf.seek(0); img = Image.open(buf)
            output = BytesIO(); img.convert("RGB").save(output, "BMP")
            data = output.getvalue()[14:]; output.close()
            if user32.OpenClipboard(0):
                try:
                    user32.EmptyClipboard()
                    h_mem = kernel32.GlobalAlloc(GMEM_MOVEABLE, len(data))
                    p_mem = kernel32.GlobalLock(h_mem)
                    ctypes.memmove(p_mem, data, len(data))
                    kernel32.GlobalUnlock(h_mem)
                    user32.SetClipboardData(CF_DIB, h_mem)
                finally:
                    user32.CloseClipboard()
                messagebox.showinfo("Success", "Graph copied!")
            else: messagebox.showerror("Error", "Clipboard busy")
        except Exception as e: messagebox.showinfo("Info", f"Copy failed: {e}")

if __name__ == "__main__":
    root = tk.Tk()
    app = IRDeconvolutionApp(root)
    root.mainloop()