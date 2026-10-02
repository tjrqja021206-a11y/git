#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
교과 7 - 조각김치 이물검출 라벨링 프로그램 (Day 2 완성형 & 이상적인 UI/UX 개선판)
================================================================================
[교육 및 실무 연계]
- 'Tkinter를 빠르게 이해하기.md'의 6대 핵심 개념(변수, 위젯, 이벤트 bind, 명령 command, 함수, mainloop) 반영
- Pasted Image 1~5(화면 구성, BBox 좌표 의미, 8개 앵커 핸들, 실시간 좌표 표시) 반영
- 4K 조각김치 고해상도 이미지 라벨링 및 YOLO 라벨 검수/보정
- 8개 앵커 핸들을 통한 BBox 미세 크기 조절(Resize) 및 자유 드래그 이동(Move) 지원
- 단일 이미지 직접 열기(1일차 1장 실습) & 폴더 전체 열기 동시 지원
- BBox 실시간 좌표/크기/YOLO비율 표시 상태바 및 마우스 추적
- Round-trip 무결성 보존 (원본 이미지 픽셀 좌표 기준 관리)
- 단축키(0~6번 클래스 즉시 지정, Del 삭제, Ctrl+Z Undo 등) 지원
- 900장 자동 무결성 검증 (QA Validation) 내장
"""

import os
import sys
import glob
import csv
import math
import copy
from datetime import datetime
import tkinter as tk
from tkinter import ttk, messagebox, filedialog

try:
    from PIL import Image, ImageTk, ImageEnhance, ImageOps
except ImportError:
    print("=" * 60)
    print("경고: Pillow 라이브러리가 설치되어 있지 않습니다.")
    print("다음 명령어로 설치 후 다시 실행해 주세요:")
    print("    pip install pillow")
    print("=" * 60)
    sys.exit(1)

# ==============================================================================
# 1. 프로젝트 공통 상수 정의 (가이드북 기준 Freeze)
# ==============================================================================

CLASSES = [
    {"id": 0, "name": "나뭇잎·종이류", "color": "#2ecc71"},       # 초록
    {"id": 1, "name": "플라스틱류·돌·금속류", "color": "#e74c3c"},   # 빨강
    {"id": 2, "name": "나뭇가지류", "color": "#0984e3"},          # 파랑
    {"id": 3, "name": "벌레류", "color": "#8e44ad"},            # 보라
    {"id": 4, "name": "고무장갑 (사용 안 함)", "color": "#7f8c8d"}, # 회색 (미사용: 발견시 REVIEW)
    {"id": 5, "name": "병해·갈변", "color": "#e67e22"},          # 주황
    {"id": 6, "name": "파·고추", "color": "#27ae60"},           # 짙은 초록
]

CLASS_MAP = {c["id"]: c for c in CLASSES}
CLASS_NAMES = [f"{c['id']} {c['name']}" for c in CLASSES]

STATUS_LIST = ["PASS", "EDITED", "REVIEW", "REVIEWED"]

SCENE_TYPES = [
    ("김치+대상", "kimchi_with_target"),
    ("정상 김치", "normal_kimchi"),
    ("객체 단독", "object_only"),
    ("기타 확인 필요", "other_review"),
]

# ==============================================================================
# 2. 메인 라벨링 애플리케이션 클래스
# ==============================================================================

class KimchiLabelingApp(tk.Tk):
    """
    [Tkinter를 빠르게 이해하기 구조 연계]
    1. 변수 (상태 기억) : bboxes, zoom, offset_x, offset_y, current_idx, is_dirty 등
    2. 화면 부품 (Widget) : Canvas(도화지), Button(명령), Label(상태표시), Treeview(목록)
    3. 이벤트 연결 (bind) : <Button-1>, <B1-Motion>, <ButtonRelease-1>, <Motion>, 단축키
    4. 명령 연결 (command) : save, next, prev, clear_bbox 등
    5. 함수 (할 일 목록) : on_mouse_down, on_mouse_drag, on_mouse_up, clear_bbox 등
    """
    def __init__(self):
        super().__init__()
        self.title("교과 7 - 조각김치 이물검출 라벨링 도구 (Day 2 완성형)")
        self.geometry("1420x940")
        self.minsize(1100, 750)

        # ----------------------------------------------------------------------
        # [변수 1] 데이터 및 파일 상태
        # ----------------------------------------------------------------------
        self.image_files = []          # 작업 이미지 전체 경로 목록
        self.filtered_indices = []     # 필터링된 인덱스 목록
        self.current_idx = -1          # 현재 이미지 인덱스
        self.current_image_path = None
        self.current_orig_image = None # 4K 원본 PIL Image
        self.orig_w = 0
        self.orig_h = 0
        
        # ----------------------------------------------------------------------
        # [변수 2] BBox 라벨 상태 (★핵심 원칙: 항상 원본 이미지 픽셀 좌표 기준!)
        # ----------------------------------------------------------------------
        self.bboxes = []               # [{"class_id": int, "x1": float, "y1": float, "x2": float, "y2": float}]
        self.original_bboxes = []       # RAW 기준 원본 BBox (Diff View용)
        self.original_bbox_count = 0
        self.show_diff = False          # RAW ↔ 현재 라벨 비교 표시
        self.enhance_brightness = 1.0   # 화면 표시용 밝기 (원본 파일 불변)
        self.enhance_contrast = 1.0     # 화면 표시용 대비 (원본 파일 불변)
        self.enhance_grayscale = False  # 화면 표시용 흑백
        self.selected_bbox_idx = None
        self.undo_stack = []           # Ctrl+Z 되돌리기 스택
        self.redo_stack = []           # Ctrl+Y / Ctrl+Shift+Z 다시 실행 스택
        
        # ----------------------------------------------------------------------
        # [변수 3] 뷰포트 상태 (Zoom & Pan)
        # ----------------------------------------------------------------------
        self.zoom = 1.0                # 화면 배율
        self.offset_x = 0.0            # 화면 X 오프셋 (캔버스 좌표계)
        self.offset_y = 0.0            # 화면 Y 오프셋
        self.fit_zoom = 1.0
        
        # ----------------------------------------------------------------------
        # [변수 4] 마우스 인터랙션 & 핸들 상태 (이미지 4 & 5 반영)
        # ----------------------------------------------------------------------
        self.pan_mode = False          # Pan 버튼 활성화 여부
        self.drag_start_x = 0
        self.drag_start_y = 0
        self.rubber_box_id = None      # 드래그 중인 임시 사각형 ID
        self.is_panning = False
        self.last_mouse_x = 0
        self.last_mouse_y = 0
        
        # BBox 편집 모드: None, "create", "move", "resize"
        self.drag_mode = None
        self.active_handle = None      # "nw", "ne", "sw", "se", "n", "s", "w", "e"
        self.move_orig_start_box = None
        self.handle_size = 7           # 앵커 핸들 네모 크기 (픽셀)
        
        # ----------------------------------------------------------------------
        # [변수 5] 저장 및 Manifest 메타데이터 상태
        # ----------------------------------------------------------------------
        self.is_dirty = False          # 수정 후 미저장 여부
        self.data_root = ""            # 작업 폴더 경로
        self.save_dir = ""             # 라벨 저장 경로 (WORK)
        self.manifest_data = {}        # image_name -> dict(상태, 작업자 등)
        
        # UI 제어 변수들
        self.current_class_id = tk.IntVar(value=2) # 기본값: 2 나뭇가지류
        self.review_status_var = tk.StringVar(value="PASS")
        self.scene_type_var = tk.StringVar(value="kimchi_with_target")
        self.assignee_var = tk.StringVar(value="A")
        self.reviewer_var = tk.StringVar(value="B")
        self.note_var = tk.StringVar(value="")
        self.warn_unsaved_var = tk.BooleanVar(value=True)
        self.show_crosshair_var = tk.BooleanVar(value=True) # 십자선 가이드
        self.filter_mode = "ALL"
        
        # UI 초기화 및 이벤트 연결
        self._init_styles()
        self._create_widgets()
        self._bind_shortcuts()
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    def _init_styles(self):
        style = ttk.Style(self)
        try:
            style.theme_use("clam")
        except Exception:
            pass

        default_font = ("Malgun Gothic", 9)
        bold_font = ("Malgun Gothic", 9, "bold")
        
        style.configure(".", font=default_font)
        style.configure("TButton", padding=4)
        style.configure("Header.TLabel", font=("Malgun Gothic", 10, "bold"))
        style.configure("Primary.TButton", font=bold_font, foreground="#0984e3")
        style.configure("Success.TButton", font=bold_font, foreground="#27ae60")
        style.configure("Danger.TButton", font=bold_font, foreground="#d63031")

    # ==========================================================================
    # UI 위젯 생성 (화면 부품 배치)
    # ==========================================================================

    def _create_widgets(self):
        # 1. 상단 툴바
        self._create_toolbar()

        # 2. 메인 분할창 (좌측 캔버스 + 우측 사이드바)
        main_paned = ttk.PanedWindow(self, orient=tk.HORIZONTAL)
        main_paned.pack(fill=tk.BOTH, expand=True, padx=5, pady=(0, 5))

        # 좌측 패널 (정보바 + 캔버스 + 실시간 좌표 상태바 + 썸네일바)
        left_frame = ttk.Frame(main_paned)
        main_paned.add(left_frame, weight=3)
        self._create_left_panel(left_frame)

        # 우측 사이드바 패널
        right_frame = ttk.Frame(main_paned, width=380)
        main_paned.add(right_frame, weight=1)
        self._create_right_panel(right_frame)

    def _create_toolbar(self):
        tb = ttk.Frame(self, padding=(6, 4))
        tb.pack(fill=tk.X, side=tk.TOP)

        # [이미지 1 & 5 반영] 단일 파일 열기 및 폴더 열기 동시 지원
        ttk.Button(tb, text="🖼️ 이미지 열기", style="Primary.TButton", command=self.open_single_image).pack(side=tk.LEFT, padx=2)
        ttk.Button(tb, text="📁 폴더 열기", command=self.open_folder).pack(side=tk.LEFT, padx=2)
        
        ttk.Separator(tb, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        ttk.Button(tb, text="💾 저장", style="Success.TButton", command=self.save_current_label).pack(side=tk.LEFT, padx=2)
        ttk.Button(tb, text="💾 저장 후 다음", command=self.save_and_next).pack(side=tk.LEFT, padx=2)
        
        ttk.Separator(tb, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)
        
        ttk.Button(tb, text="⬅️ 이전 (A)", command=self.prev_image).pack(side=tk.LEFT, padx=2)
        ttk.Button(tb, text="➡️ 다음 (D)", command=self.next_image).pack(side=tk.LEFT, padx=2)

        ttk.Separator(tb, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        ttk.Button(tb, text="🔍 Fit (F)", command=self.zoom_fit).pack(side=tk.LEFT, padx=2)
        ttk.Button(tb, text="🔍 Zoom +", command=lambda: self.zoom_step(1.25)).pack(side=tk.LEFT, padx=2)
        ttk.Button(tb, text="🔍 Zoom -", command=lambda: self.zoom_step(0.8)).pack(side=tk.LEFT, padx=2)
        
        self.pan_btn = ttk.Button(tb, text="✋ Pan", command=self.toggle_pan_mode)
        self.pan_btn.pack(side=tk.LEFT, padx=2)

        ttk.Separator(tb, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)

        ttk.Button(tb, text="↩️ Undo", command=self.undo_bbox).pack(side=tk.LEFT, padx=2)
        ttk.Button(tb, text="↪️ Redo", command=self.redo_bbox).pack(side=tk.LEFT, padx=2)
        # [이미지 5 반영] clear_bbox 전체 삭제 버튼
        ttk.Button(tb, text="🗑️ 전체 삭제", style="Danger.TButton", command=self.clear_bbox).pack(side=tk.LEFT, padx=2)
        ttk.Button(tb, text="🛡️ Validation", command=self.run_validation).pack(side=tk.LEFT, padx=2)

        ttk.Separator(tb, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=5)
        ttk.Button(tb, text="🔍 Diff View", command=self.toggle_diff_view).pack(side=tk.LEFT, padx=2)
        ttk.Button(tb, text="☀ 밝기", command=self.cycle_brightness).pack(side=tk.LEFT, padx=2)
        ttk.Button(tb, text="◐ 대비", command=self.cycle_contrast).pack(side=tk.LEFT, padx=2)
        ttk.Button(tb, text="◑ 흑백", command=self.toggle_grayscale).pack(side=tk.LEFT, padx=2)

        # 우측 줌 및 가이드 표시
        self.zoom_label = ttk.Label(tb, text="Zoom: 100%", foreground="#636e72")
        self.zoom_label.pack(side=tk.RIGHT, padx=6)
        
        chk_cross = ttk.Checkbutton(tb, text="십자선", variable=self.show_crosshair_var, command=self.render_canvas)
        chk_cross.pack(side=tk.RIGHT, padx=6)

    def _create_left_panel(self, parent):
        # 상단 정보 바 (파일명 / 진행률)
        info_bar = ttk.Frame(parent, padding=(4, 2))
        info_bar.pack(fill=tk.X, side=tk.TOP)

        self.filename_label = ttk.Label(info_bar, text="파일 이름 : (파일을 불러와 주세요)", style="Header.TLabel")
        self.filename_label.pack(side=tk.LEFT)

        self.progress_label = ttk.Label(info_bar, text="진행률 0 / 0", style="Header.TLabel", foreground="#0984e3")
        self.progress_label.pack(side=tk.RIGHT)

        # 메인 도화지 (Canvas)
        canvas_frame = ttk.Frame(parent, relief=tk.SUNKEN, borderwidth=1)
        canvas_frame.pack(fill=tk.BOTH, expand=True, padx=2, pady=2)

        self.canvas = tk.Canvas(canvas_frame, bg="#2d3436", highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True)

        # [이벤트 연결: bind] 'Tkinter를 빠르게 이해하기'의 마우스 4대 이벤트
        self.canvas.bind("<ButtonPress-1>", self.on_mouse_down)
        self.canvas.bind("<B1-Motion>", self.on_mouse_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_mouse_up)
        self.canvas.bind("<Motion>", self.on_mouse_move) # 십자선 & 좌표추적 & 커서변경
        
        # 우클릭 Pan 드래그 바인딩
        self.canvas.bind("<ButtonPress-3>", self._on_pan_start)
        self.canvas.bind("<B3-Motion>", self._on_pan_motion)
        self.canvas.bind("<ButtonRelease-3>", self._on_pan_end)
        
        # 마우스 휠 줌 (Windows & Linux)
        self.canvas.bind("<MouseWheel>", self._on_mouse_wheel)
        self.canvas.bind("<Button-4>", lambda e: self.zoom_step(1.15, e.x, e.y))
        self.canvas.bind("<Button-5>", lambda e: self.zoom_step(0.85, e.x, e.y))
        self.canvas.bind("<Configure>", self._on_canvas_resize)

        # ----------------------------------------------------------------------
        # [이미지 1, 2, 4, 5 반영] 하단 실시간 BBox 좌표 & 크기 상태 표시줄
        # ----------------------------------------------------------------------
        coord_bar = ttk.Frame(parent, padding=(6, 3), relief=tk.GROOVE)
        coord_bar.pack(fill=tk.X, side=tk.TOP, pady=2)

        self.bbox_info_label = ttk.Label(
            coord_bar,
            text="BBox : 선택 없음    Width: 0, Height: 0",
            font=("Consolas", 9, "bold"),
            foreground="#2d3436"
        )
        self.bbox_info_label.pack(side=tk.LEFT, padx=4)

        self.mouse_coord_label = ttk.Label(
            coord_bar,
            text="마우스 원본 좌표: (0, 0)",
            font=("Consolas", 8),
            foreground="#636e72"
        )
        self.mouse_coord_label.pack(side=tk.RIGHT, padx=6)

        # 하단 썸네일 네비게이션 바
        thumb_bar = ttk.Frame(parent, padding=(4, 2))
        thumb_bar.pack(fill=tk.X, side=tk.BOTTOM)

        ttk.Label(thumb_bar, text="이미지 목록 : ", font=("Malgun Gothic", 9, "bold")).pack(side=tk.LEFT, padx=2)
        ttk.Button(thumb_bar, text="◀ 이전 5개", width=9, command=lambda: self.shift_thumbnails(-5)).pack(side=tk.LEFT, padx=2)

        self.thumb_container = ttk.Frame(thumb_bar)
        self.thumb_container.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=4)

        ttk.Button(thumb_bar, text="다음 5개 ▶", width=9, command=lambda: self.shift_thumbnails(5)).pack(side=tk.RIGHT, padx=2)

    def _create_right_panel(self, parent):
        canvas = tk.Canvas(parent, highlightthickness=0)
        scrollbar = ttk.Scrollbar(parent, orient=tk.VERTICAL, command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas, padding=(6, 4))

        scrollable_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw", width=360)
        canvas.configure(yscrollcommand=scrollbar.set)

        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        # 1. 클래스 선택
        cls_box = ttk.LabelFrame(scrollable_frame, text=" ▎ 클래스 선택 (단축키 0~6) ", padding=6)
        cls_box.pack(fill=tk.X, pady=(0, 5))

        self.class_combo = ttk.Combobox(cls_box, values=CLASS_NAMES, state="readonly", font=("Malgun Gothic", 9))
        self.class_combo.current(2) # 기본값: 2 나뭇가지류
        self.class_combo.pack(fill=tk.X, pady=(0, 4))
        self.class_combo.bind("<<ComboboxSelected>>", self._on_class_combo_change)

        cls_list_frame = ttk.Frame(cls_box)
        cls_list_frame.pack(fill=tk.X)

        for c in CLASSES:
            row = ttk.Frame(cls_list_frame)
            row.pack(fill=tk.X, pady=1)

            color_box = tk.Label(row, bg=c["color"], width=2, height=1, relief=tk.SOLID, borderwidth=1)
            color_box.pack(side=tk.LEFT, padx=(2, 6))

            text = f"{c['id']}  {c['name']}"
            lbl = tk.Label(row, text=text, anchor="w", cursor="hand2", font=("Malgun Gothic", 8))
            lbl.pack(side=tk.LEFT, fill=tk.X, expand=True)
            lbl.bind("<Button-1>", lambda e, cid=c["id"]: self._select_class(cid))
            color_box.bind("<Button-1>", lambda e, cid=c["id"]: self._select_class(cid))

        # 2. 라벨 목록
        lbl_box = ttk.LabelFrame(scrollable_frame, text=" ▎ 라벨 목록 (0개) ", padding=6)
        lbl_box.pack(fill=tk.X, pady=(0, 5))
        self.lbl_box_title = lbl_box

        columns = ("No", "클래스", "위치 (x,y,w,h)", "상태")
        self.tree = ttk.Treeview(lbl_box, columns=columns, show="headings", height=5)
        self.tree.heading("No", text="No")
        self.tree.heading("클래스", text="클래스")
        self.tree.heading("위치 (x,y,w,h)", text="위치 (x, y, w, h)")
        self.tree.heading("상태", text="상태")

        self.tree.column("No", width=30, anchor="center")
        self.tree.column("클래스", width=115, anchor="w")
        self.tree.column("위치 (x,y,w,h)", width=135, anchor="center")
        self.tree.column("상태", width=55, anchor="center")

        tree_scroll = ttk.Scrollbar(lbl_box, orient=tk.VERTICAL, command=self.tree.yview)
        self.tree.configure(yscrollcommand=tree_scroll.set)
        
        self.tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        tree_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.tree.bind("<<TreeviewSelect>>", self._on_tree_select)

        # 라벨 관리 버튼들
        btn_row = ttk.Frame(scrollable_frame)
        btn_row.pack(fill=tk.X, pady=(0, 5))
        ttk.Button(btn_row, text="선택 BBox 삭제 (Del)", style="Danger.TButton", command=self.delete_selected_bbox).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=1)
        ttk.Button(btn_row, text="선택 클래스 변경", command=self.change_selected_bbox_class).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=1)

        # 3. 검수 상태 & 작업자 정보
        stat_frame = ttk.Frame(scrollable_frame)
        stat_frame.pack(fill=tk.X, pady=(0, 5))

        box_review = ttk.LabelFrame(stat_frame, text=" ▎ 검수 상태 ", padding=6)
        box_review.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 3))

        for s in STATUS_LIST:
            rb = ttk.Radiobutton(box_review, text=s, value=s, variable=self.review_status_var, command=self._on_metadata_change)
            rb.pack(anchor="w", pady=1)

        box_worker = ttk.LabelFrame(stat_frame, text=" ▎ 작업자 정보 ", padding=6)
        box_worker.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(3, 0))

        ttk.Label(box_worker, text="작업자:").grid(row=0, column=0, sticky="w", pady=2)
        e_assignee = ttk.Entry(box_worker, textvariable=self.assignee_var, width=10)
        e_assignee.grid(row=0, column=1, sticky="ew", pady=2)
        e_assignee.bind("<KeyRelease>", lambda e: self._on_metadata_change())

        ttk.Label(box_worker, text="검수자:").grid(row=1, column=0, sticky="w", pady=2)
        e_reviewer = ttk.Entry(box_worker, textvariable=self.reviewer_var, width=10)
        e_reviewer.grid(row=1, column=1, sticky="ew", pady=2)
        e_reviewer.bind("<KeyRelease>", lambda e: self._on_metadata_change())

        # 4. Scene Type & Issue Note
        scene_frame = ttk.Frame(scrollable_frame)
        scene_frame.pack(fill=tk.X, pady=(0, 5))

        box_scene = ttk.LabelFrame(scene_frame, text=" ▎ Scene Type ", padding=6)
        box_scene.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 3))

        for text, val in SCENE_TYPES:
            rb = ttk.Radiobutton(box_scene, text=text, value=val, variable=self.scene_type_var, command=self._on_metadata_change)
            rb.pack(anchor="w", pady=1)

        box_note = ttk.LabelFrame(scene_frame, text=" ▎ Issue / Note ", padding=6)
        box_note.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(3, 0))

        self.note_entry = tk.Text(box_note, height=5, width=14, font=("Malgun Gothic", 8))
        self.note_entry.pack(fill=tk.BOTH, expand=True)
        self.note_entry.bind("<KeyRelease>", lambda e: self._on_metadata_change())

        # 5. CSV 저장 정보 미리보기
        box_csv = ttk.LabelFrame(scrollable_frame, text=" ▎ CSV 저장 정보 (Manifest) ", padding=6)
        box_csv.pack(fill=tk.X, pady=(0, 5))

        self.csv_preview_lbl = tk.Label(
            box_csv,
            text="status = PASS\nassignee = A\nreviewer = B\nscene_type = kimchi_with_target",
            justify=tk.LEFT,
            anchor="w",
            font=("Consolas", 8),
            bg="#f1f2f6",
            padx=6,
            pady=4,
            relief=tk.SUNKEN
        )
        self.csv_preview_lbl.pack(fill=tk.X)

        # 6. 필터 / QA 도구
        box_filter = ttk.LabelFrame(scrollable_frame, text=" ▎ 필터 / QA 도구 ", padding=6)
        box_filter.pack(fill=tk.X, pady=(0, 5))

        filter_btn_row = ttk.Frame(box_filter)
        filter_btn_row.pack(fill=tk.X, pady=2)
        ttk.Button(filter_btn_row, text="REVIEW만 보기", command=lambda: self.apply_filter("REVIEW")).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=1)
        ttk.Button(filter_btn_row, text="EDITED만 보기", command=lambda: self.apply_filter("EDITED")).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=1)
        ttk.Button(filter_btn_row, text="전체 보기", command=lambda: self.apply_filter("ALL")).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=1)

        warn_chk = ttk.Checkbutton(box_filter, text="미저장 경고 팝업 활성화", variable=self.warn_unsaved_var)
        warn_chk.pack(anchor="w", pady=2)

    def _bind_shortcuts(self):
        """키보드 단축키 연결"""
        self.bind("<Left>", lambda e: self.prev_image())
        self.bind("<Right>", lambda e: self.next_image())
        self.bind("<a>", lambda e: self.prev_image())
        self.bind("<d>", lambda e: self.next_image())
        self.bind("<Control-s>", lambda e: self.save_current_label())
        self.bind("<Control-w>", lambda e: self.save_and_next())
        self.bind("<w>", lambda e: self.save_and_next())
        self.bind("<Delete>", lambda e: self.delete_selected_bbox())
        self.bind("<Control-z>", lambda e: self.undo_bbox())
        self.bind("<Control-y>", lambda e: self.redo_bbox())
        self.bind("<Control-Shift-Z>", lambda e: self.redo_bbox())
        self.bind("<f>", lambda e: self.zoom_fit())
        self.bind("<plus>", lambda e: self.zoom_step(1.25))
        self.bind("<equal>", lambda e: self.zoom_step(1.25))
        self.bind("<minus>", lambda e: self.zoom_step(0.8))
        
        # 숫자키 0~6: 클래스 즉시 변경/지정
        for cid in range(7):
            self.bind(str(cid), lambda e, c=cid: self._select_class(c))

    # ==========================================================================
    # 파일 열기 & 데이터 로드
    # ==========================================================================

    def open_single_image(self):
        """[이미지 1 & 5 반영] 단일 JPG/PNG 파일 열기 (1일차 1장 End-to-End 실습용)"""
        fpath = filedialog.askopenfilename(
            title="라벨링할 이미지 파일을 선택하세요",
            filetypes=[("Image files", "*.jpg *.jpeg *.png *.JPG *.JPEG *.PNG"), ("All files", "*.*")]
        )
        if not fpath or not os.path.exists(fpath):
            return

        self.data_root = os.path.dirname(os.path.abspath(fpath))
        self.image_files = [os.path.abspath(fpath)]
        self.filtered_indices = [0]
        self._determine_save_dir()
        self._load_manifest()
        self.load_image_at_index(0)
        self.update_thumbnail_strip()

    def open_folder(self, target_dir=None):
        """전체 폴더 열기 (900장 대량 작업용)"""
        if not target_dir:
            target_dir = filedialog.askdirectory(title="작업할 데이터 폴더를 선택하세요")
        if not target_dir or not os.path.exists(target_dir):
            return

        self.data_root = os.path.abspath(target_dir)

        patterns = ["*.jpg", "*.jpeg", "*.png", "*.JPG", "*.JPEG", "*.PNG"]
        found_files = []
        for pat in patterns:
            found_files.extend(glob.glob(os.path.join(self.data_root, pat)))
            found_files.extend(glob.glob(os.path.join(self.data_root, "**", pat), recursive=True))

        found_files = sorted(list(set(found_files)))

        filtered = [f for f in found_files if not os.path.basename(f).startswith("Pasted image") and not "images" in os.path.dirname(f).lower() or any(p in f for p in ["train", "validation", "김치", "이물", "data"])]
        if not filtered and found_files:
            filtered = found_files

        if not filtered:
            messagebox.showwarning("파일 없음", f"선택한 폴더에서 JPG/PNG 이미지를 찾을 수 없습니다:\n{self.data_root}")
            return

        self.image_files = filtered
        self.filtered_indices = list(range(len(self.image_files)))
        self._determine_save_dir()
        self._load_manifest()

        self.current_idx = 0
        self.load_image_at_index(self.filtered_indices[0])
        self.update_thumbnail_strip()

    def _determine_save_dir(self):
        """저장할 라벨 디렉터리 결정 (RAW 원본 보존, WORK 분리)"""
        first_img = self.image_files[0]
        img_dir = os.path.dirname(first_img)

        if "raw" in img_dir.lower():
            self.save_dir = img_dir.lower().replace("raw", "work").replace("images", "labels")
        elif "images" in img_dir:
            parent = os.path.dirname(img_dir)
            split = os.path.basename(img_dir)
            self.save_dir = os.path.join(parent, "labels", split)
        else:
            self.save_dir = os.path.join(img_dir, "labels_work")

        os.makedirs(self.save_dir, exist_ok=True)

    def _find_yolo_txt(self, img_path):
        base_name = os.path.splitext(os.path.basename(img_path))[0]
        img_dir = os.path.dirname(img_path)

        work_txt = os.path.join(self.save_dir, base_name + ".txt")
        if os.path.exists(work_txt):
            return work_txt

        same_txt = os.path.join(img_dir, base_name + ".txt")
        if os.path.exists(same_txt):
            return same_txt

        parent = os.path.dirname(img_dir)
        sub = os.path.basename(img_dir)
        cand1 = os.path.join(parent, "labels", sub, base_name + ".txt")
        if os.path.exists(cand1):
            return cand1
        cand2 = os.path.join(parent, "labels", base_name + ".txt")
        if os.path.exists(cand2):
            return cand2

        cand_list = glob.glob(os.path.join(self.data_root, "**", base_name + ".txt"), recursive=True)
        if cand_list:
            return cand_list[0]

        return None

    # ==========================================================================
    # 이미지 로드 & 좌표계 렌더링
    # ==========================================================================

    def _find_original_yolo_txt(self, img_path):
        """WORK보다 우선하지 않고 RAW/원본 후보만 찾아 Diff 기준으로 사용합니다."""
        base_name = os.path.splitext(os.path.basename(img_path))[0]
        img_dir = os.path.dirname(img_path)
        candidates = []

        # 현재 이미지가 raw 아래에 있다면 대응되는 원본 labels 경로를 먼저 확인
        raw_dir = img_dir
        if "work" in raw_dir.lower():
            raw_dir = raw_dir.lower().replace("work", "raw")
        if "labels" in raw_dir.lower():
            candidates.append(os.path.join(raw_dir, base_name + ".txt"))

        parent = os.path.dirname(img_dir)
        sub = os.path.basename(img_dir)
        candidates.extend([
            os.path.join(parent, "labels", sub, base_name + ".txt"),
            os.path.join(parent, "raw", "labels", sub, base_name + ".txt"),
            os.path.join(parent, "raw", sub, base_name + ".txt"),
        ])

        # 전체 검색 시 WORK 저장 폴더는 제외
        for cand in candidates:
            if os.path.exists(cand) and os.path.normpath(cand) != os.path.normpath(os.path.join(self.save_dir, base_name + ".txt")):
                return cand

        for cand in glob.glob(os.path.join(self.data_root, "**", base_name + ".txt"), recursive=True):
            low = cand.lower()
            if "work" not in low and "final" not in low:
                return cand
        return None

    def _bbox_iou(self, a, b):
        ax1, ay1 = min(a["x1"], a["x2"]), min(a["y1"], a["y2"])
        ax2, ay2 = max(a["x1"], a["x2"]), max(a["y1"], a["y2"])
        bx1, by1 = min(b["x1"], b["x2"]), min(b["y1"], b["y2"])
        bx2, by2 = max(b["x1"], b["x2"]), max(b["y1"], b["y2"])
        ix1, iy1, ix2, iy2 = max(ax1, bx1), max(ay1, by1), min(ax2, bx2), min(ay2, by2)
        iw, ih = max(0.0, ix2 - ix1), max(0.0, iy2 - iy1)
        inter = iw * ih
        area_a = max(0.0, ax2 - ax1) * max(0.0, ay2 - ay1)
        area_b = max(0.0, bx2 - bx1) * max(0.0, by2 - by1)
        union = area_a + area_b - inter
        return inter / union if union > 0 else 0.0

    def _diff_matches(self):
        """RAW와 현재 BBox를 IoU+class 기준으로 greedy 매칭합니다."""
        matches = []
        used_current = set()
        for oi, old in enumerate(self.original_bboxes):
            best = None
            for ci, cur in enumerate(self.bboxes):
                if ci in used_current or old.get("class_id") != cur.get("class_id"):
                    continue
                score = self._bbox_iou(old, cur)
                if best is None or score > best[0]:
                    best = (score, ci)
            if best is not None and best[0] >= 0.25:
                used_current.add(best[1])
                matches.append((oi, best[1], best[0]))
        matched_old = {x[0] for x in matches}
        matched_cur = {x[1] for x in matches}
        added = [i for i in range(len(self.bboxes)) if i not in matched_cur]
        deleted = [i for i in range(len(self.original_bboxes)) if i not in matched_old]
        modified = [ci for oi, ci, iou in matches if iou < 0.90]
        unchanged = [ci for oi, ci, iou in matches if iou >= 0.90]
        return matches, added, deleted, modified, unchanged

    def toggle_diff_view(self):
        self.show_diff = not self.show_diff
        self.render_canvas()

    def cycle_brightness(self):
        levels = [1.0, 0.75, 1.25, 1.5, 1.0]
        try:
            idx = levels.index(self.enhance_brightness)
        except ValueError:
            idx = 0
        self.enhance_brightness = levels[(idx + 1) % len(levels)]
        self.render_canvas()

    def cycle_contrast(self):
        levels = [1.0, 0.75, 1.25, 1.5, 1.0]
        try:
            idx = levels.index(self.enhance_contrast)
        except ValueError:
            idx = 0
        self.enhance_contrast = levels[(idx + 1) % len(levels)]
        self.render_canvas()

    def toggle_grayscale(self):
        self.enhance_grayscale = not self.enhance_grayscale
        self.render_canvas()

    def _apply_display_enhancement(self, image):
        """원본 PIL Image는 건드리지 않고 화면 표시용 사본에만 필터를 적용합니다."""
        result = image
        if self.enhance_brightness != 1.0:
            result = ImageEnhance.Brightness(result).enhance(self.enhance_brightness)
        if self.enhance_contrast != 1.0:
            result = ImageEnhance.Contrast(result).enhance(self.enhance_contrast)
        if self.enhance_grayscale:
            result = ImageOps.grayscale(result).convert("RGB")
        return result

    def _draw_diff_overlay(self):
        if not self.show_diff:
            return
        matches, added, deleted, modified, unchanged = self._diff_matches()

        # RAW: 회색 점선 / 현재: 일반 BBox 위에 변경 상태를 추가 강조
        for oi, old in enumerate(self.original_bboxes):
            x1, y1 = self._orig_to_canvas(old["x1"], old["y1"])
            x2, y2 = self._orig_to_canvas(old["x2"], old["y2"])
            self.canvas.create_rectangle(
                min(x1, x2), min(y1, y2), max(x1, x2), max(y1, y2),
                outline="#dfe6e9", width=2, dash=(5, 3), tags=("diff_raw",)
            )

        for idx in deleted:
            old = self.original_bboxes[idx]
            x1, y1 = self._orig_to_canvas(old["x1"], old["y1"])
            x2, y2 = self._orig_to_canvas(old["x2"], old["y2"])
            self.canvas.create_rectangle(min(x1,x2), min(y1,y2), max(x1,x2), max(y1,y2), outline="#ff4757", width=4)
            self.canvas.create_text(min(x1,x2), min(y1,y2)-4, text="삭제", fill="#ff4757", anchor="sw", font=("Malgun Gothic", 8, "bold"))

        for idx in added:
            b = self.bboxes[idx]
            x1, y1 = self._orig_to_canvas(b["x1"], b["y1"])
            x2, y2 = self._orig_to_canvas(b["x2"], b["y2"])
            self.canvas.create_rectangle(min(x1,x2), min(y1,y2), max(x1,x2), max(y1,y2), outline="#2ed573", width=4)
            self.canvas.create_text(min(x1,x2), min(y1,y2)-4, text="추가", fill="#2ed573", anchor="sw", font=("Malgun Gothic", 8, "bold"))

        for idx in modified:
            b = self.bboxes[idx]
            x1, y1 = self._orig_to_canvas(b["x1"], b["y1"])
            x2, y2 = self._orig_to_canvas(b["x2"], b["y2"])
            self.canvas.create_rectangle(min(x1,x2), min(y1,y2), max(x1,x2), max(y1,y2), outline="#ffa502", width=4)
            self.canvas.create_text(min(x1,x2), min(y1,y2)-4, text="수정", fill="#ffa502", anchor="sw", font=("Malgun Gothic", 8, "bold"))

        self.canvas.create_rectangle(8, 8, 255, 74, fill="#2f3542", outline="#57606f")
        self.canvas.create_text(16, 18, text="DIFF VIEW", fill="white", anchor="w", font=("Malgun Gothic", 9, "bold"))
        self.canvas.create_text(16, 36, text=f"추가 {len(added)}   수정 {len(modified)}   삭제 {len(deleted)}", fill="white", anchor="w", font=("Malgun Gothic", 8))
        self.canvas.create_text(16, 54, text=f"변경없음 {len(unchanged)}   RAW {len(self.original_bboxes)} → 현재 {len(self.bboxes)}", fill="#dfe6e9", anchor="w", font=("Malgun Gothic", 8))

    def _update_enhancement_label(self):
        if hasattr(self, "enhance_label"):
            gray = "ON" if self.enhance_grayscale else "OFF"
            self.enhance_label.config(text=f"B:{self.enhance_brightness:.2f}  C:{self.enhance_contrast:.2f}  G:{gray}")

    def load_image_at_index(self, target_idx):
        if not (0 <= target_idx < len(self.image_files)):
            return

        if self.is_dirty and self.warn_unsaved_var.get():
            res = messagebox.askyesnocancel("미저장 변경 알림", "현재 이미지의 라벨이 수정되었습니다.\n저장하시겠습니까?")
            if res is True:
                self.save_current_label()
            elif res is None:
                return

        self.current_idx = target_idx
        self.current_image_path = self.image_files[target_idx]
        self.undo_stack.clear()
        self.redo_stack.clear()
        self.selected_bbox_idx = None
        self.drag_mode = None

        try:
            self.current_orig_image = Image.open(self.current_image_path).convert("RGB")
            self.orig_w, self.orig_h = self.current_orig_image.size
        except Exception as e:
            messagebox.showerror("이미지 로드 오류", f"이미지를 열 수 없습니다:\n{e}")
            return

        self.bboxes = []
        txt_path = self._find_yolo_txt(self.current_image_path)
        if txt_path and os.path.exists(txt_path):
            self.bboxes = self._parse_yolo_txt(txt_path)

        # RAW 기준 라벨도 별도로 읽어 Diff View의 기준으로 보존합니다.
        original_txt_path = self._find_original_yolo_txt(self.current_image_path)
        if original_txt_path and os.path.exists(original_txt_path):
            self.original_bboxes = self._parse_yolo_txt(original_txt_path)
        else:
            self.original_bboxes = copy.deepcopy(self.bboxes)

        self.original_bbox_count = len(self.original_bboxes)
        self.show_diff = False
        self.is_dirty = False

        self._restore_manifest_info()

        fname = os.path.basename(self.current_image_path)
        self.filename_label.config(text=f"파일 이름 : {fname} ({self.orig_w}×{self.orig_h})")
        self.progress_label.config(text=f"진행률 {self.current_idx + 1} / {len(self.image_files)}")

        self.zoom_fit()
        self._update_table()
        self._update_bbox_status_label()
        self.update_thumbnail_strip()

    def _parse_yolo_txt(self, txt_path):
        """YOLO TXT 파싱 -> 원본 픽셀 좌표 리스트 변환"""
        parsed = []
        try:
            with open(txt_path, "r", encoding="utf-8") as f:
                for line in f:
                    parts = line.strip().split()
                    if len(parts) >= 5:
                        cid = int(parts[0])
                        cx, cy, w, h = map(float, parts[1:5])

                        center_x = cx * self.orig_w
                        center_y = cy * self.orig_h
                        box_w = w * self.orig_w
                        box_h = h * self.orig_h

                        x1 = center_x - box_w / 2.0
                        y1 = center_y - box_h / 2.0
                        x2 = center_x + box_w / 2.0
                        y2 = center_y + box_h / 2.0

                        parsed.append({
                            "class_id": cid,
                            "x1": max(0.0, min(float(self.orig_w), x1)),
                            "y1": max(0.0, min(float(self.orig_h), y1)),
                            "x2": max(0.0, min(float(self.orig_w), x2)),
                            "y2": max(0.0, min(float(self.orig_h), y2))
                        })
        except Exception as e:
            print(f"TXT 읽기 오류: {e}")
        return parsed

    def render_canvas(self):
        """[화면 갱신] 4K 뷰포트 고속 크롭 렌더링 + BBox 및 8개 앵커 핸들 드로잉"""
        if not self.current_orig_image:
            return

        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()
        if cw <= 10 or ch <= 10:
            return

        self.canvas.delete("all")

        # 1. 4K 보이는 영역만 스마트 크롭 렌더링
        crop_x1 = max(0, int((-self.offset_x) / self.zoom))
        crop_y1 = max(0, int((-self.offset_y) / self.zoom))
        crop_x2 = min(self.orig_w, int((cw - self.offset_x) / self.zoom + 1))
        crop_y2 = min(self.orig_h, int((ch - self.offset_y) / self.zoom + 1))

        if crop_x2 > crop_x1 and crop_y2 > crop_y1:
            cropped = self.current_orig_image.crop((crop_x1, crop_y1, crop_x2, crop_y2))
            cropped = self._apply_display_enhancement(cropped)
            disp_w = int(round((crop_x2 - crop_x1) * self.zoom))
            disp_h = int(round((crop_y2 - crop_y1) * self.zoom))

            if disp_w > 0 and disp_h > 0:
                resized = cropped.resize((disp_w, disp_h), Image.Resampling.BILINEAR)
                self.tk_image = ImageTk.PhotoImage(resized)

                place_x = int(round(crop_x1 * self.zoom + self.offset_x))
                place_y = int(round(crop_y1 * self.zoom + self.offset_y))
                self.canvas.create_image(place_x, place_y, anchor="nw", image=self.tk_image)

        # 2. BBox 렌더링
        for idx, bbox in enumerate(self.bboxes):
            self._draw_bbox_on_canvas(idx, bbox)

        # 3. RAW ↔ 현재 라벨 변경점 오버레이
        self._draw_diff_overlay()
        self._update_enhancement_label()

        self.zoom_label.config(text=f"Zoom: {int(self.zoom * 100)}%")

    def _draw_bbox_on_canvas(self, idx, bbox):
        """BBox 사각형 + 클래스 뱃지 + [이미지 5] 8개 앵커 핸들 그리기"""
        x1, y1 = self._orig_to_canvas(bbox["x1"], bbox["y1"])
        x2, y2 = self._orig_to_canvas(bbox["x2"], bbox["y2"])

        left = min(x1, x2)
        right = max(x1, x2)
        top = min(y1, y2)
        bottom = max(y1, y2)

        cid = bbox["class_id"]
        c_info = CLASS_MAP.get(cid, {"name": f"Class {cid}", "color": "#f1c40f"})
        color = c_info["color"]
        c_name = c_info["name"]

        is_selected = (idx == self.selected_bbox_idx)
        outline_width = 3 if is_selected else 2
        rect_color = "#f1c40f" if is_selected else color

        # 사각형
        self.canvas.create_rectangle(
            left, top, right, bottom,
            outline=rect_color,
            width=outline_width,
            tags=("bbox", f"bbox_{idx}")
        )

        # 뱃지 태그
        tag_text = f" {c_name} "
        badge_h = 16
        badge_y1 = max(0, top - badge_h)
        badge_y2 = badge_y1 + badge_h
        badge_w = len(tag_text) * 8 + 6
        badge_x2 = left + badge_w

        self.canvas.create_rectangle(left, badge_y1, badge_x2, badge_y2, fill=color, outline=color)
        self.canvas.create_text(
            left + 3, badge_y1 + 8,
            text=tag_text,
            fill="white",
            anchor="w",
            font=("Malgun Gothic", 8, "bold")
        )

        # [이미지 5 반영] 선택된 BBox인 경우 8개 앵커 핸들 그리기
        if is_selected:
            handles = self._get_handle_positions(left, top, right, bottom)
            hs = self.handle_size
            for h_name, (hx, hy) in handles.items():
                self.canvas.create_rectangle(
                    hx - hs // 2, hy - hs // 2,
                    hx + hs // 2, hy + hs // 2,
                    fill="white", outline="#d63031", width=2,
                    tags=("handle", f"handle_{h_name}")
                )

    def _get_handle_positions(self, l, t, r, b):
        """8개 앵커 핸들의 화면 좌표 계산"""
        mx = (l + r) / 2.0
        my = (t + b) / 2.0
        return {
            "nw": (l, t),
            "n":  (mx, t),
            "ne": (r, t),
            "w":  (l, my),
            "e":  (r, my),
            "sw": (l, b),
            "s":  (mx, b),
            "se": (r, b)
        }

    # ==========================================================================
    # 좌표 변환 수식 (가이드북 15, 16, 41절)
    # ==========================================================================

    def _orig_to_canvas(self, ox, oy):
        cx = ox * self.zoom + self.offset_x
        cy = oy * self.zoom + self.offset_y
        return cx, cy

    def _canvas_to_orig(self, cx, cy):
        ox = (cx - self.offset_x) / self.zoom
        oy = (cy - self.offset_y) / self.zoom
        ox = max(0.0, min(float(self.orig_w), ox))
        oy = max(0.0, min(float(self.orig_h), oy))
        return ox, oy

    # ==========================================================================
    # 줌 / 팬 동작
    # ==========================================================================

    def zoom_fit(self):
        if not self.current_orig_image:
            return
        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()
        if cw <= 10 or ch <= 10:
            return

        scale_w = (cw - 20) / self.orig_w
        scale_h = (ch - 20) / self.orig_h
        self.zoom = min(scale_w, scale_h, 1.0)
        self.fit_zoom = self.zoom

        disp_w = self.orig_w * self.zoom
        disp_h = self.orig_h * self.zoom
        self.offset_x = (cw - disp_w) / 2.0
        self.offset_y = (ch - disp_h) / 2.0

        self.render_canvas()

    def zoom_step(self, factor, center_x=None, center_y=None):
        if not self.current_orig_image:
            return

        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()
        if center_x is None: center_x = cw / 2.0
        if center_y is None: center_y = ch / 2.0

        new_zoom = max(0.05, min(8.0, self.zoom * factor))
        if new_zoom == self.zoom:
            return

        orig_center_x = (center_x - self.offset_x) / self.zoom
        orig_center_y = (center_y - self.offset_y) / self.zoom

        self.zoom = new_zoom
        self.offset_x = center_x - orig_center_x * self.zoom
        self.offset_y = center_y - orig_center_y * self.zoom

        self.render_canvas()

    def _on_mouse_wheel(self, event):
        if event.delta > 0:
            self.zoom_step(1.15, event.x, event.y)
        else:
            self.zoom_step(0.85, event.x, event.y)

    def toggle_pan_mode(self):
        self.pan_mode = not self.pan_mode
        if self.pan_mode:
            self.pan_btn.config(text="✋ Pan (ON)")
            self._set_cursor("fleur")
        else:
            self.pan_btn.config(text="✋ Pan")
            self._set_cursor("crosshair")

    def _on_pan_start(self, event):
        self.is_panning = True
        self.last_mouse_x = event.x
        self.last_mouse_y = event.y

    def _on_pan_motion(self, event):
        if self.is_panning:
            dx = event.x - self.last_mouse_x
            dy = event.y - self.last_mouse_y
            self.offset_x += dx
            self.offset_y += dy
            self.last_mouse_x = event.x
            self.last_mouse_y = event.y
            self.render_canvas()

    def _on_pan_end(self, event):
        self.is_panning = False

    def _on_canvas_resize(self, event):
        if self.current_orig_image and self.zoom == self.fit_zoom:
            self.zoom_fit()
        else:
            self.render_canvas()

    def _set_cursor(self, cursor_name):
        """운영체제별(Windows / WSL Linux) 안전한 커서 변경"""
        try:
            self.canvas.config(cursor=cursor_name)
        except Exception:
            try:
                self.canvas.config(cursor="crosshair")
            except Exception:
                pass

    # ==========================================================================
    # 마우스 인터랙션: BBox 그리기, 앵커 핸들 리사이즈, 이동
    # [Tkinter를 빠르게 이해하기 핵심 함수 4개 매핑]
    # ==========================================================================

    def on_mouse_down(self, event):
        """마우스를 누른 순간 (시작 좌표 기억, 핸들/BBox 선택 판정)"""
        if self.pan_mode:
            self._on_pan_start(event)
            return

        self.drag_start_x = event.x
        self.drag_start_y = event.y
        self.last_mouse_x = event.x
        self.last_mouse_y = event.y

        # 1. 현재 선택된 BBox의 8개 앵커 핸들 클릭 여부 확인 (Resize 모드)
        if self.selected_bbox_idx is not None and 0 <= self.selected_bbox_idx < len(self.bboxes):
            h_name = self._hit_test_handles(event.x, event.y, self.selected_bbox_idx)
            if h_name:
                self.drag_mode = "resize"
                self.active_handle = h_name
                self._save_undo_state()
                return

        # 2. BBox 내부 클릭 여부 확인 (Move 모드 또는 선택)
        clicked_idx = self._find_bbox_at(event.x, event.y)
        if clicked_idx is not None:
            self.selected_bbox_idx = clicked_idx
            self.drag_mode = "move"
            self.move_orig_start_box = copy.deepcopy(self.bboxes[clicked_idx])
            self._save_undo_state()
            self._update_table()
            self._update_bbox_status_label()
