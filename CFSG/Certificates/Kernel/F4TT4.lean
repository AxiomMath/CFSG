module

public import CFSG.Certificates.Kernel.F4TKS
public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Maximal
import all CFSG.Fischer.F4
import all CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Bridge
import all CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Checks

public section

namespace CFSG.KC.F4T

open CFSG.Fischer CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisN
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Light CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Bridge
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Elem

@[expose] def ImgIn (M N : Matrix (Fin 3) (Fin 3) F4) (Om : List (List Nat)) : Prop :=
  ∀ v ∈ Om, ∃ u ∈ Om, ∃ c : F4, c ≠ 0 ∧ Matrix.mulVec M (vecT v) = c • Matrix.mulVec N (vecT u)

@[expose] def PtsOK (Om : List (List Nat)) : Prop := ∀ v ∈ Om, (∀ x ∈ v, x < 4) ∧ vecT v ≠ 0

theorem ptT_proj_bool : (List.range 64).all (fun n => (List.range 64).all fun m =>
    !(ptT (n / 16) (n / 4 % 4) (n % 4) == ptT (m / 16) (m / 4 % 4) (m % 4)) || n == 0 || m == 0 ||
    (n / 16 == mT 1 (m / 16) && n / 4 % 4 == mT 1 (m / 4 % 4) && n % 4 == mT 1 (m % 4)) ||
    (n / 16 == mT 2 (m / 16) && n / 4 % 4 == mT 2 (m / 4 % 4) && n % 4 == mT 2 (m % 4)) ||
    (n / 16 == mT 3 (m / 16) && n / 4 % 4 == mT 3 (m / 4 % 4) && n % 4 == mT 3 (m % 4))) =
      true := by
  decide +kernel

theorem ptT_proj_num : ∀ n < 64, ∀ m < 64,
    ptT (n / 16) (n / 4 % 4) (n % 4) = ptT (m / 16) (m / 4 % 4) (m % 4) → n ≠ 0 → m ≠ 0 →
    (n / 16 = mT 1 (m / 16) ∧ n / 4 % 4 = mT 1 (m / 4 % 4) ∧ n % 4 = mT 1 (m % 4)) ∨
    (n / 16 = mT 2 (m / 16) ∧ n / 4 % 4 = mT 2 (m / 4 % 4) ∧ n % 4 = mT 2 (m % 4)) ∨
    (n / 16 = mT 3 (m / 16) ∧ n / 4 % 4 = mT 3 (m / 4 % 4) ∧ n % 4 = mT 3 (m % 4)) := by
  intro n hn m hm he hn0 hm0
  have H := ptT_proj_bool
  rw [List.all_eq_true] at H
  have H2 := H n (List.mem_range.2 hn)
  rw [List.all_eq_true] at H2
  have H3 := H2 m (List.mem_range.2 hm)
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne]
    at H3
  rcases H3 with ((((h | h) | h) | h) | h) | h
  · exact absurd he h
  · exact absurd h hn0
  · exact absurd h hm0
  · exact Or.inl (and_assoc.1 h)
  · exact Or.inr (Or.inl (and_assoc.1 h))
  · exact Or.inr (Or.inr (and_assoc.1 h))

theorem ptT_proj_codes : ∀ x0 < 4, ∀ x1 < 4, ∀ x2 < 4, ∀ y0 < 4, ∀ y1 < 4, ∀ y2 < 4,
    ptT x0 x1 x2 = ptT y0 y1 y2 → ¬(x0 = 0 ∧ x1 = 0 ∧ x2 = 0) → ¬(y0 = 0 ∧ y1 = 0 ∧ y2 = 0) →
    (x0 = mT 1 y0 ∧ x1 = mT 1 y1 ∧ x2 = mT 1 y2) ∨ (x0 = mT 2 y0 ∧ x1 = mT 2 y1 ∧ x2 = mT 2 y2) ∨
      (x0 = mT 3 y0 ∧ x1 = mT 3 y1 ∧ x2 = mT 3 y2) := by
  intro x0 h0 x1 h1 x2 h2 y0 k0 y1 k1 y2 k2 h hx hy
  have ex0 : (16 * x0 + 4 * x1 + x2) / 16 = x0 := by omega
  have ex1 : (16 * x0 + 4 * x1 + x2) / 4 % 4 = x1 := by omega
  have ex2 : (16 * x0 + 4 * x1 + x2) % 4 = x2 := by omega
  have ey0 : (16 * y0 + 4 * y1 + y2) / 16 = y0 := by omega
  have ey1 : (16 * y0 + 4 * y1 + y2) / 4 % 4 = y1 := by omega
  have ey2 : (16 * y0 + 4 * y1 + y2) % 4 = y2 := by omega
  have := ptT_proj_num (16 * x0 + 4 * x1 + x2) (by omega) (16 * y0 + 4 * y1 + y2) (by omega)
  rw [ex0, ex1, ex2, ey0, ey1, ey2] at this
  exact this h (by omega) (by omega)

theorem ptT_proj_all {x0 x1 x2 y0 y1 y2 : Nat} (h0 : x0 < 4) (h1 : x1 < 4) (h2 : x2 < 4)
    (k0 : y0 < 4) (k1 : y1 < 4) (k2 : y2 < 4) (h : ptT x0 x1 x2 = ptT y0 y1 y2)
    (hx : ¬(x0 = 0 ∧ x1 = 0 ∧ x2 = 0)) (hy : ¬(y0 = 0 ∧ y1 = 0 ∧ y2 = 0)) :
    ∃ c : F4, c ≠ 0 ∧ f4 x0 = c * f4 y0 ∧ f4 x1 = c * f4 y1 ∧ f4 x2 = c * f4 y2 := by
  have hc : ∀ c < 4, c ≠ 0 → x0 = mT c y0 ∧ x1 = mT c y1 ∧ x2 = mT c y2 →
      ∃ c : F4, c ≠ 0 ∧ f4 x0 = c * f4 y0 ∧ f4 x1 = c * f4 y1 ∧ f4 x2 = c * f4 y2 := by
    rintro c hc4 hc0 ⟨rfl, rfl, rfl⟩
    exact ⟨f4 c, fun e => hc0 (f4_eq_zero c hc4 e), f4_mT hc4 k0, f4_mT hc4 k1, f4_mT hc4 k2⟩
  rcases ptT_proj_codes _ h0 _ h1 _ h2 _ k0 _ k1 _ k2 h hx hy with e | e | e
  · exact hc 1 (by decide) (by decide) e
  · exact hc 2 (by decide) (by decide) e
  · exact hc 3 (by decide) (by decide) e

theorem mulVec_toMT_vecT {A : M3 Nat} (hA : OK A) {v : List Nat} (hv : ∀ x ∈ v, x < 4) :
    Matrix.mulVec (toMT A) (vecT v) =
      ![f4 (dotT A.a00 A.a01 A.a02 (v.getD 0 0) (v.getD 1 0) (v.getD 2 0)),
        f4 (dotT A.a10 A.a11 A.a12 (v.getD 0 0) (v.getD 1 0) (v.getD 2 0)),
        f4 (dotT A.a20 A.a21 A.a22 (v.getD 0 0) (v.getD 1 0) (v.getD 2 0))] := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hA
  have h0 := getD_lt hv 0
  have h1 := getD_lt hv 1
  have h2 := getD_lt hv 2
  rw [f4_dotT a0 a1 a2 h0 h1 h2, f4_dotT a3 a4 a5 h0 h1 h2, f4_dotT a6 a7 a8 h0 h1 h2]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, toMT, toMat, toLT, vecT]

theorem mulVec_ne_zero_of_det {M : Matrix (Fin 3) (Fin 3) F4} (hd : M.det ≠ 0)
    {x : Fin 3 → F4} (hx : x ≠ 0) : Matrix.mulVec M x ≠ 0 := by
  intro h
  apply hx
  have hinj : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hd))
  exact hinj (h.trans (Matrix.mulVec_zero M).symm)

theorem imgT_proj {v v' : List Nat} (hv : ∀ x ∈ v, x < 4) (hv' : ∀ x ∈ v', x < 4)
    {A B : M3 Nat} (hA : OK A) (hB : OK B) (hA0 : Matrix.mulVec (toMT A) (vecT v) ≠ 0)
    (hB0 : Matrix.mulVec (toMT B) (vecT v') ≠ 0) (h : imgT A v = imgT B v') :
    ∃ c : F4, c ≠ 0 ∧ Matrix.mulVec (toMT A) (vecT v) = c • Matrix.mulVec (toMT B) (vecT v') := by
  rw [mulVec_toMT_vecT hA hv] at hA0 ⊢
  rw [mulVec_toMT_vecT hB hv'] at hB0 ⊢
  dsimp only [imgT] at h
  have nz : ∀ {x0 x1 x2 : Nat}, ![f4 x0, f4 x1, f4 x2] ≠ 0 → ¬(x0 = 0 ∧ x1 = 0 ∧ x2 = 0) := by
    rintro x0 x1 x2 hne ⟨rfl, rfl, rfl⟩
    apply hne
    ext i
    fin_cases i <;> rfl
  obtain ⟨c, hc, e0, e1, e2⟩ := ptT_proj_all (dotT_lt _ _ _ _ _ _) (dotT_lt _ _ _ _ _ _)
    (dotT_lt _ _ _ _ _ _) (dotT_lt _ _ _ _ _ _) (dotT_lt _ _ _ _ _ _) (dotT_lt _ _ _ _ _ _)
    h (nz hA0) (nz hB0)
  refine ⟨c, hc, ?_⟩
  funext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2

theorem hmaskT_testBit (A : M3 Nat) (Om : List (List Nat)) (k : Nat) :
    (hmaskT A Om).testBit k = true ↔ ∃ v ∈ Om, imgT A v = k := by
  have key : ∀ (L : List (List Nat)) (acc : Nat),
      (L.foldl (fun m v => Nat.lor m (Nat.shiftLeft 1 (imgT A v))) acc).testBit k = true ↔
        acc.testBit k = true ∨ ∃ v ∈ L, imgT A v = k := by
    intro L
    induction L with
    | nil => intro acc; simp
    | cons v L ih =>
      intro acc
      rw [List.foldl_cons, ih]
      change (acc ||| 1 <<< imgT A v).testBit k = true ∨ _ ↔ _
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨u, hu, hk⟩)
        · exact Or.inl h
        · exact Or.inr ⟨v, Or.inl rfl, h⟩
        · exact Or.inr ⟨u, Or.inr hu, hk⟩
      · rintro (h | ⟨u, rfl | hu, hk⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr hk)
        · exact Or.inr ⟨u, hu, hk⟩
  rw [hmaskT, key]
  simp

theorem hmaskT_sound {Om : List (List Nat)} (hOm : PtsOK Om) {A B : M3 Nat} (hA : OK A)
    (hB : OK B) (hdA : (toMT A).det ≠ 0) (hdB : (toMT B).det ≠ 0)
    (h : hmaskT A Om = hmaskT B Om) : ImgIn (toMT A) (toMT B) Om := by
  intro v hv
  have hk : (hmaskT A Om).testBit (imgT A v) = true := (hmaskT_testBit A Om _).2 ⟨v, hv, rfl⟩
  rw [h] at hk
  obtain ⟨u, hu, hBu⟩ := (hmaskT_testBit B Om _).1 hk
  obtain ⟨hvl, hv0⟩ := hOm v hv
  obtain ⟨hul, hu0⟩ := hOm u hu
  exact ⟨u, hu, imgT_proj hvl hul hA hB (mulVec_ne_zero_of_det hdA hv0)
    (mulVec_ne_zero_of_det hdB hu0) hBu.symm⟩

theorem ImgIn_trans {M N G N' : Matrix (Fin 3) (Fin 3) F4} {Om : List (List Nat)}
    (h1 : ImgIn M N Om) (h2 : ImgIn (G * N) N' Om) : ImgIn (G * M) N' Om := by
  intro v hv
  obtain ⟨u, hu, c, hc, hMv⟩ := h1 v hv
  obtain ⟨u', hu', c', hc', hGu⟩ := h2 u hu
  refine ⟨u', hu', c * c', mul_ne_zero hc hc', ?_⟩
  rw [← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGu, smul_smul]

theorem f4_aT6 {x1 x2 x3 x4 x5 x6 : Nat} (h1 : x1 < 4) (h2 : x2 < 4) (h3 : x3 < 4) (h4 : x4 < 4)
    (h5 : x5 < 4) (h6 : x6 < 4) :
    f4 (aT (aT (aT x1 x2) (aT x3 x4)) (aT x5 x6)) =
      f4 x1 + f4 x2 + (f4 x3 + f4 x4) + (f4 x5 + f4 x6) := by
  rw [f4_aT (aT_lt (aT_lt h1 h2) (aT_lt h3 h4)) (aT_lt h5 h6),
    f4_aT (aT_lt h1 h2) (aT_lt h3 h4), f4_aT h1 h2, f4_aT h3 h4, f4_aT h5 h6]

theorem f4_m3 {a b c : Nat} (ha : a < 4) (hb : b < 4) (hc : c < 4) :
    f4 (mT (mT a b) c) = f4 a * f4 b * f4 c := by
  rw [f4_mT (mT_lt a b) hc, f4_mT ha hb]

theorem f4_detT {A : M3 Nat} (hA : OK A) : (toMT A).det = f4 (detT A) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := hA
  rw [toMT, det_toMat]
  unfold detT
  rw [f4_aT6 (mT_lt _ _) (mT_lt _ _) (mT_lt _ _) (mT_lt _ _) (mT_lt _ _) (mT_lt _ _),
    f4_m3 a0 a4 a8, f4_m3 a0 a5 a7, f4_m3 a1 a3 a8, f4_m3 a1 a5 a6, f4_m3 a2 a3 a7,
    f4_m3 a2 a4 a6]
  simp only [detL, toLT, CharTwo.sub_eq_add]
  ring

theorem det_ne_zero_of_detT {A : M3 Nat} (hA : OK A) (h : detT A = 1) : (toMT A).det ≠ 0 := by
  rw [f4_detT hA, h, f4_one]
  exact one_ne_zero

theorem inT_spec {l : List Nat} {x : Nat} (h : inT l x = true) : ∃ m ∈ l, x = m := by
  unfold inT at h
  obtain ⟨m, hm, he⟩ := List.any_eq_true.1 h
  exact ⟨m, hm, Nat.eq_of_beq_eq_true he⟩

theorem snd_mem_zip {α β : Type} {l₁ : List α} {l₂ : List β} (hlen : l₁.length = l₂.length)
    {b : β} (hb : b ∈ l₂) : ∃ a, (a, b) ∈ l₁.zip l₂ := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  have hi' : i < l₁.length := by rw [hlen]; exact hi
  exact ⟨l₁[i], List.mem_iff_getElem.2 ⟨i, by simp [List.length_zip, hi, hi'], by simp⟩⟩

theorem fst_mem_zip {α β : Type} {l₁ : List α} {l₂ : List β} (hlen : l₁.length = l₂.length)
    {a : α} (ha : a ∈ l₁) : ∃ b, (a, b) ∈ l₁.zip l₂ := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi' : i < l₂.length := by rw [← hlen]; exact hi
  exact ⟨l₂[i], List.mem_iff_getElem.2 ⟨i, by simp [List.length_zip, hi, hi'], by simp⟩⟩

theorem closeOK_spec {Om : List (List Nat)} {reps : List (List Nat)} {ms : List Nat}
    (h : closeOK Om reps ms = true) :
    (∃ R ∈ reps, hmaskT (matN R) Om = hmaskT mOne Om) ∧
      ∀ R ∈ reps, codeOK R = true ∧ detT (matN R) = 1 ∧
        ∀ g ∈ gens7T, ∃ R' ∈ reps, hmaskT (mMulT g (matN R)) Om = hmaskT (matN R') Om := by
  simp only [closeOK, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at h
  obtain ⟨⟨hlen, hin⟩, hall⟩ := h
  have hrow : ∀ R m, (R, m) ∈ reps.zip ms → codeOK R = true ∧ detT (matN R) = 1 ∧
      hmaskT (matN R) Om = m ∧ ∀ g ∈ gens7T, inT ms (hmaskT (mMulT g (matN R)) Om) = true := by
    intro R m hRm
    have := hall _ hRm
    simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  have hmask : ∀ m ∈ ms, ∃ R ∈ reps, hmaskT (matN R) Om = m := by
    intro m hm
    obtain ⟨R, hR⟩ := snd_mem_zip hlen hm
    exact ⟨R, (List.of_mem_zip hR).1, (hrow R m hR).2.2.1⟩
  refine ⟨?_, fun R hR => ?_⟩
  · obtain ⟨m, hm, hx⟩ := inT_spec hin
    obtain ⟨R, hR, hRm⟩ := hmask m hm
    exact ⟨R, hR, hRm.trans hx.symm⟩
  · obtain ⟨m, hRm⟩ := fst_mem_zip hlen hR
    obtain ⟨hc, hd, _, hg⟩ := hrow R m hRm
    refine ⟨hc, hd, fun g hgm => ?_⟩
    obtain ⟨m', hm', hx⟩ := inT_spec (hg g hgm)
    obtain ⟨R', hR', hR'm⟩ := hmask m' hm'
    exact ⟨R', hR', hx.trans hR'm.symm⟩

theorem gens7T_OK : ∀ g ∈ gens7T, ∀ x ∈ [g.a00, g.a01, g.a02, g.a10, g.a11, g.a12, g.a20, g.a21,
    g.a22], x < 4 := by decide

theorem gens7T_detT : ∀ g ∈ gens7T, detT g = 1 := by decide

@[expose] def S7 : Set (Matrix.GeneralLinearGroup (Fin 3) F4) :=
  {u | ∃ g ∈ gens7T, (u : Matrix (Fin 3) (Fin 3) F4) = toMT g}

theorem InM_S7 {g : M3 Nat} (hg : g ∈ gens7T) : InM (Subgroup.closure S7) (toMT g) := by
  have hd : (toMT g).det = 1 := by
    rw [f4_detT (OK_of_lt (gens7T_OK g hg)), gens7T_detT g hg, f4_one]
  exact ⟨unitOfDet1 _ hd, Subgroup.subset_closure ⟨g, hg, coe_unitOfDet1 _ hd⟩,
    coe_unitOfDet1 _ hd⟩

theorem SL_le_S7 : SLsub ≤ Subgroup.closure S7 := by
  have hX : InM (Subgroup.closure S7) Xd := by
    rw [← toMT_xdT]
    exact InM_S7 (by simp [gens7T])
  have hE : ∀ M ∈ esT.map toMT, InM (Subgroup.closure S7) M := by
    intro M hM
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hM
    exact InM_S7 (List.mem_cons_of_mem _ he)
  rw [toMT_esT] at hE
  exact SLsub_le_of_words hX (InM_mul hX hX) (hE _ (by simp)) (hE _ (by simp)) (hE _ (by simp))
    (hE _ (by simp)) (hE _ (by simp)) (hE _ (by simp))

theorem orbit_of_closeOK {Om : List (List Nat)} (hOm : PtsOK Om) {reps : List (List Nat)}
    {ms : List Nat} (h : closeOK Om reps ms = true) :
    ∀ y ∈ SLsub, ∃ R ∈ reps, ImgIn (y : Matrix (Fin 3) (Fin 3) F4) (toMT (matN R)) Om := by
  obtain ⟨⟨R0, hR0, hm0⟩, hall⟩ := closeOK_spec h
  let Q : Matrix.GeneralLinearGroup (Fin 3) F4 → Prop := fun y =>
    ∃ R ∈ reps, ImgIn (y : Matrix (Fin 3) (Fin 3) F4) (toMT (matN R)) Om
  have hstep : ∀ x ∈ S7, ∀ y, Q y → Q (x * y) := by
    rintro x ⟨g, hg, hxg⟩ y ⟨R, hR, himg⟩
    obtain ⟨hc, hd, hcl⟩ := hall R hR
    obtain ⟨R', hR', hm⟩ := hcl g hg
    obtain ⟨hc', hd', _⟩ := hall R' hR'
    have hgOK := OK_of_lt (gens7T_OK g hg)
    have hROK := matN_OK hc
    have hdg : (toMT (mMulT g (matN R))).det ≠ 0 := by
      rw [toMT_mMulT hgOK hROK, Matrix.det_mul, f4_detT hgOK, f4_detT hROK, gens7T_detT g hg, hd,
        f4_one, one_mul]
      exact one_ne_zero
    have h2 := hmaskT_sound hOm (mMulT_OK _ _) (matN_OK hc') hdg
      (det_ne_zero_of_detT (matN_OK hc') hd') hm
    rw [toMT_mMulT hgOK hROK] at h2
    refine ⟨R', hR', ?_⟩
    rw [Units.val_mul, hxg]
    exact ImgIn_trans himg h2
  have hone : Q 1 := by
    refine ⟨R0, hR0, ?_⟩
    obtain ⟨hc0, hd0, _⟩ := hall R0 hR0
    have h1 := hmaskT_sound hOm mOne_OK (matN_OK hc0) (by rw [toMT_mOne, Matrix.det_one]; exact one_ne_zero)
      (det_ne_zero_of_detT (matN_OK hc0) hd0) hm0.symm
    rw [toMT_mOne] at h1
    rw [Units.val_one]
    exact h1
  have hpow : ∀ x ∈ S7, ∀ (k : Nat) y, Q y → Q (x ^ k * y) := by
    intro x hx k
    induction k with
    | zero => intro y hy; rw [pow_zero, one_mul]; exact hy
    | succ k ih => intro y hy; rw [pow_succ', mul_assoc]; exact hstep x hx _ (ih y hy)
  intro y hy
  refine Subgroup.closure_induction_left (p := fun y _ => Q y) hone
    (fun x hx y _ hQ => hstep x hx y hQ) (fun x hx y _ hQ => ?_) (SL_le_S7 hy)
  have hpos : 0 < orderOf x := orderOf_pos x
  have h1 : x * x ^ (orderOf x - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [← eq_inv_of_mul_eq_one_right h1]
  exact hpow x hx _ y hQ

theorem cover_of_ImgIn {i : Fin 6} {Om : List (List Nat)}
    (hΩ : ∀ v, v ∈ Omega i ↔ ∃ d ∈ Om, vecT d = v) {M N : Matrix (Fin 3) (Fin 3) F4}
    (h : ImgIn M N Om) :
    ∀ v ∈ Omega i, ∃ u ∈ Omega i, ∃ c : F4, c ≠ 0 ∧ Matrix.mulVec M v = c • Matrix.mulVec N u := by
  intro v hv
  obtain ⟨d, hd, rfl⟩ := (hΩ v).1 hv
  obtain ⟨u, hu, c, hc, he⟩ := h d hd
  exact ⟨vecT u, (hΩ _).2 ⟨u, hu, rfl⟩, c, hc, he⟩

theorem stab_of_ImgIn {i : Fin 6} {Om : List (List Nat)}
    (hΩ : ∀ v, v ∈ Omega i ↔ ∃ d ∈ Om, vecT d = v) {M : Matrix (Fin 3) (Fin 3) F4}
    (h : ImgIn M 1 Om) : stabilizes i M := by
  intro v hv
  obtain ⟨u, hu, c, hc, he⟩ := cover_of_ImgIn hΩ h v hv
  rw [Matrix.one_mulVec] at he
  exact ⟨u, hu, c, hc, he⟩

theorem t4WordsOK_spec {Om : List (List Nat)} {r : List Nat} {reps : List (List Nat)}
    {ws : List (List (List Nat))} (h : t4WordsOK Om r reps ws = true) :
    codeOK r = true ∧ detT (matN r) = 1 ∧ hmaskT (matN r) Om = hmaskT mOne Om ∧
      ∀ R ∈ reps, codeOK R = true ∧ ∃ w, w6OK [xdT, wmT 1, zsT, matN r, matN R] w = true := by
  simp only [t4WordsOK, Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hc, hd⟩, hm⟩, hlen⟩, hall⟩ := h
  refine ⟨hc, hd, hm, fun R hR => ?_⟩
  obtain ⟨w, hw⟩ := fst_mem_zip hlen hR
  have := hall _ hw
  simp only [Bool.and_eq_true] at this
  exact ⟨this.1, w, this.2⟩

theorem t4WordsOK_append {Om : List (List Nat)} {r : List Nat} {L₁ L₂ : List (List Nat)}
    {W₁ W₂ : List (List (List Nat))} (h₁ : t4WordsOK Om r L₁ W₁ = true)
    (h₂ : t4WordsOK Om r L₂ W₂ = true) : t4WordsOK Om r (L₁ ++ L₂) (W₁ ++ W₂) = true := by
  simp only [t4WordsOK, Bool.and_eq_true, Nat.beq_eq] at h₁ h₂ ⊢
  refine ⟨⟨h₁.1.1, by rw [List.length_append, List.length_append, h₁.1.2, h₂.1.2]⟩, ?_⟩
  rw [List.zip_append h₁.1.2, List.all_append, h₁.2, h₂.2]
  rfl

theorem T4_of_data (i : Fin 6) {Om : List (List Nat)}
    (hΩ : ∀ v, v ∈ Omega i ↔ ∃ d ∈ Om, vecT d = v) (hOm : PtsOK Om) {r : List Nat}
    {reps : List (List Nat)} {ms : List Nat} {ws : List (List (List Nat))}
    (hclose : closeOK Om reps ms = true) (hhead : reps.head? = some [1, 0, 0, 0, 1, 0, 0, 0, 1])
    (hw : t4WordsOK Om r reps.tail ws = true) (Y : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F4)) :
    P i < Y → Y ≤ SLsub → Y = SLsub := by
  intro hPY hYS
  have hPle : P i ≤ Y := hPY.le
  obtain ⟨y, hyY, hyP⟩ := SetLike.exists_of_lt hPY
  have hdety : (y : Matrix (Fin 3) (Fin 3) F4).det = 1 := hYS hyY
  obtain ⟨R, hR, himg⟩ := orbit_of_closeOK hOm hclose y (hYS hyY)
  have hcov := cover_of_ImgIn hΩ himg
  obtain ⟨hcR, hdR, _⟩ := (closeOK_spec hclose).2 R hR
  have hROK := matN_OK hcR
  obtain ⟨R0, tl, rfl⟩ : ∃ (R0 : List Nat) (tl : List (List Nat)), reps = R0 :: tl := by
    cases reps with
    | nil => exact absurd hhead (by simp)
    | cons a l => exact ⟨a, l, rfl⟩
  have hR0 : R0 = [1, 0, 0, 0, 1, 0, 0, 0, 1] := Option.some.inj hhead
  rcases List.mem_cons.1 hR with rfl | hRt
  · exfalso
    apply hyP
    refine mem_P.2 ⟨hdety, fun v hv => ?_⟩
    obtain ⟨u, hu, c, hc, he⟩ := hcov v hv
    have h1 : toMT (matN [1, 0, 0, 0, 1, 0, 0, 0, 1]) = 1 := toMT_mOne
    rw [hR0, h1, Matrix.one_mulVec] at he
    exact ⟨u, hu, c, hc, he⟩
  · have hRdet : (toMT (matN R)).det = 1 := by rw [f4_detT hROK, hdR, f4_one]
    have hRY : InM Y (toMT (matN R)) := T4_core hPle hyY hdety hRdet hcov
    obtain ⟨hcr, hdr, hmr, hws⟩ := t4WordsOK_spec hw
    obtain ⟨_, w, hwR⟩ := hws R hRt
    have hrOK := matN_OK hcr
    have hrdet : (toMT (matN r)).det = 1 := by rw [f4_detT hrOK, hdr, f4_one]
    have hrs : stabilizes i (toMT (matN r)) := by
      have h1 := hmaskT_sound hOm hrOK mOne_OK (by rw [hrdet]; exact one_ne_zero)
        (by rw [toMT_mOne, Matrix.det_one]; exact one_ne_zero) hmr
      rw [toMT_mOne] at h1
      exact stab_of_ImgIn hΩ h1
    have hX : InM Y Xd := InM_of_P hPle det_Xd (stab_Xd i)
    obtain ⟨o1, _, o3, _⟩ := consts_OK
    have hgens : GensIn Y [xdT, wmT 1, zsT, matN r, matN R] := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl
      · exact ⟨o1, by rw [toMT_xdT]; exact hX⟩
      · refine ⟨wmT_OK (by decide), ?_⟩
        rw [toMT_wmT, f4_one]
        exact InM_of_P hPle det_Wm1 (stab_Wm1 i)
      · exact ⟨o3, by rw [toMT_zsT]; exact InM_of_P hPle det_Zs (stab_Zs i)⟩
      · exact ⟨hrOK, InM_of_P hPle hrdet hrs⟩
      · exact ⟨hROK, hRY⟩
    exact le_antisymm hYS (SL_of_w6OK hgens hX hwR)

end CFSG.KC.F4T

end
