module

public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.IVK.L2BN

open Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] noncomputable def uT (t : F) : GL (Fin 2) F := uHom F (Multiplicative.ofAdd t)

@[expose] def dg (a d : Fˣ) : GL (Fin 2) F where
  val := !![(a : F), 0; 0, (d : F)]
  inv := !![((a⁻¹ : Fˣ) : F), 0; 0, ((d⁻¹ : Fˣ) : F)]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp

@[simp] theorem uT_val (t : F) : (uT t : GL (Fin 2) F).val = !![1, t; 0, 1] := rfl

@[simp] theorem uT_inv_val (t : F) : ((uT t)⁻¹ : GL (Fin 2) F).val = !![1, -t; 0, 1] := rfl

@[simp] theorem dg_val (a d : Fˣ) :
    (dg a d : GL (Fin 2) F).val = !![(a : F), 0; 0, (d : F)] := rfl

@[simp] theorem dg_inv_val (a d : Fˣ) :
    ((dg a d)⁻¹ : GL (Fin 2) F).val = !![((a⁻¹ : Fˣ) : F), 0; 0, ((d⁻¹ : Fˣ) : F)] := rfl

@[simp] theorem wGL_val : (wGL F).val = !![0, 1; -1, 0] := rfl

@[simp] theorem wGL_inv_val : ((wGL F)⁻¹ : GL (Fin 2) F).val = !![0, -1; 1, 0] := rfl

theorem GL2_ext {g h : GL (Fin 2) F} (h00 : g.1 0 0 = h.1 0 0) (h01 : g.1 0 1 = h.1 0 1)
    (h10 : g.1 1 0 = h.1 1 0) (h11 : g.1 1 1 = h.1 1 1) : g = h := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem mul_val_apply (g h : GL (Fin 2) F) (i j : Fin 2) :
    (g * h).1 i j = g.1 i 0 * h.1 0 j + g.1 i 1 * h.1 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mem_statedSL_iff (g : GL (Fin 2) F) :
    g ∈ StatedSL 2 F ↔ g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := by
  have h : StatedSL 2 F = (Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker := by
    have : {A : GL (Fin 2) F | (A : Matrix (Fin 2) (Fin 2) F).det = 1} =
        ((Matrix.GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker : Set (GL (Fin 2) F)) := by
      ext A
      simp [Units.ext_iff]
    rw [StatedSL, this, Subgroup.closure_eq]
  rw [h, MonoidHom.mem_ker]
  simp [Units.ext_iff, Matrix.det_fin_two]

theorem det_ne_zero (g : GL (Fin 2) F) : g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 ≠ 0 := by
  have := (Matrix.isUnit_iff_isUnit_det (g : Matrix (Fin 2) (Fin 2) F)).1 g.isUnit
  rw [Matrix.det_fin_two] at this
  exact this.ne_zero

theorem mem_diagGL_iff (g : GL (Fin 2) F) : g ∈ diagGL F ↔ g.1 0 1 = 0 ∧ g.1 1 0 = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · rintro ⟨h01, h10⟩
    have hdet := det_ne_zero g
    rw [h01, h10] at hdet
    have h00 : g.1 0 0 ≠ 0 := left_ne_zero_of_mul (by simpa using hdet)
    have h11 : g.1 1 1 ≠ 0 := right_ne_zero_of_mul (by simpa using hdet)
    refine ⟨fun i => Units.mk0 (g.1 i i) (by fin_cases i <;> assumption), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10]

theorem mem_range_uHom_iff (g : GL (Fin 2) F) :
    g ∈ (uHom F).range ↔ g.1 0 0 = 1 ∧ g.1 1 1 = 1 ∧ g.1 1 0 = 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    simp [uHom]
  · rintro ⟨h00, h11, h10⟩
    refine ⟨Multiplicative.ofAdd (g.1 0 1), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uHom, h00, h11, h10]

theorem mem_range_uHom_iff' (g : GL (Fin 2) F) : g ∈ (uHom F).range ↔ ∃ t : F, g = uT t := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.toAdd t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.ofAdd t, rfl⟩

theorem uT_mem_range (t : F) : uT t ∈ (uHom F).range := ⟨Multiplicative.ofAdd t, rfl⟩

theorem uT_mul (s t : F) : uT s * uT t = uT (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem uT_zero : uT (0 : F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem uT_mem_statedSL (t : F) : uT t ∈ StatedSL 2 F := by
  simp [mem_statedSL_iff]

theorem wGL_mem_statedSL : wGL F ∈ StatedSL 2 F := by
  simp [mem_statedSL_iff]

theorem dg_mem_statedSL {a d : Fˣ} (h : (a : F) * d = 1) : dg a d ∈ StatedSL 2 F := by
  simp [mem_statedSL_iff, h]

theorem dg_mem_diagGL (a d : Fˣ) : dg a d ∈ diagGL F := by
  simp [mem_diagGL_iff]

theorem exists_ne_inv [Finite F] (h3 : 3 < Nat.card F) : ∃ a : Fˣ, (a : F) ≠ (a : F)⁻¹ := by
  by_contra hcon
  push Not at hcon
  classical
  have := Fintype.ofFinite F
  have hle : Nat.card F ≤ 3 := by
    rw [Nat.card_eq_fintype_card]
    calc Fintype.card F = (Finset.univ : Finset F).card := Finset.card_univ.symm
      _ ≤ ({0, 1, -1} : Finset F).card := Finset.card_le_card (fun x _ => by
          by_cases hx : x = 0
          · simp [hx]
          · have h := hcon (Units.mk0 x hx)
            simp only [Units.val_mk0] at h
            have h2 : x * x = 1 := by
              calc x * x = x * x⁻¹ := by rw [← h]
                _ = 1 := mul_inv_cancel₀ hx
            have h3 : (x - 1) * (x + 1) = 0 := by linear_combination h2
            rcases mul_eq_zero.1 h3 with h4 | h4
            · simp [sub_eq_zero.1 h4]
            · simp [eq_neg_of_add_eq_zero_left h4])
      _ ≤ 3 := Finset.card_le_three
  omega

theorem c_eq_zero_of_mem_normalizer_U {g : GL (Fin 2) F}
    (h : g ∈ normalizer (((uHom F).range : Subgroup (GL (Fin 2) F)) : Set (GL (Fin 2) F))) :
    g.1 1 0 = 0 := by
  rw [Subgroup.mem_normalizer_iff] at h
  obtain ⟨t, ht⟩ := (mem_range_uHom_iff' _).1 ((h (uT 1)).1 (uT_mem_range 1))
  have ht' : uT t * g = g * uT 1 := by
    rw [← ht]
    group
  have := congrArg (fun m : GL (Fin 2) F => m.1 1 1) ht'
  simpa [Matrix.mul_apply, Fin.sum_univ_two] using this

theorem diag_conj_U {g : GL (Fin 2) F} (hg : g ∈ diagGL F) {h : GL (Fin 2) F}
    (hh : h ∈ (uHom F).range) : g * h * g⁻¹ ∈ (uHom F).range := by
  obtain ⟨t, rfl⟩ := (mem_range_uHom_iff' h).1 hh
  rw [mem_diagGL_iff] at hg
  obtain ⟨hg01, hg10⟩ := hg
  have hdet := det_ne_zero g
  rw [hg01, hg10] at hdet
  have h11 : g.1 1 1 ≠ 0 := right_ne_zero_of_mul (by simpa using hdet)
  have : g * uT t * g⁻¹ = uT (g.1 0 0 * t / g.1 1 1) := by
    rw [mul_inv_eq_iff_eq_mul]
    apply GL2_ext
    all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, hg01, hg10]
    field_simp
  rw [this]
  exact uT_mem_range _

theorem diag_mem_normalizer_U {g : GL (Fin 2) F} (hg : g ∈ diagGL F) :
    g ∈ normalizer (((uHom F).range : Subgroup (GL (Fin 2) F)) : Set (GL (Fin 2) F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨diag_conj_U hg, fun h' => ?_⟩
  have := diag_conj_U (inv_mem hg) h'
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at this

theorem diag_or_antidiag {g k : GL (Fin 2) F} {a : Fˣ} (ha : (a : F) ≠ (a : F)⁻¹)
    (hk : k ∈ diagGL F) (h : g * dg a a⁻¹ * g⁻¹ = k) :
    (g.1 0 1 = 0 ∧ g.1 1 0 = 0) ∨ (g.1 0 0 = 0 ∧ g.1 1 1 = 0) := by
  rw [mem_diagGL_iff] at hk
  obtain ⟨hk01, hk10⟩ := hk
  rw [mul_inv_eq_iff_eq_mul] at h
  have e00 := congrArg (fun m : GL (Fin 2) F => m.1 0 0) h
  have e01 := congrArg (fun m : GL (Fin 2) F => m.1 0 1) h
  have e10 := congrArg (fun m : GL (Fin 2) F => m.1 1 0) h
  have e11 := congrArg (fun m : GL (Fin 2) F => m.1 1 1) h
  simp [Matrix.mul_apply, Fin.sum_univ_two, hk01, hk10] at e00 e01 e10 e11
  have hdet := det_ne_zero g
  have hne : (a : F)⁻¹ - (a : F) ≠ 0 := sub_ne_zero.2 ha.symm
  by_cases h00 : g.1 0 0 = 0
  · right
    refine ⟨h00, ?_⟩
    rw [h00] at hdet
    have h01 : g.1 0 1 ≠ 0 := left_ne_zero_of_mul (by simpa using hdet)
    have h10 : g.1 1 0 ≠ 0 := right_ne_zero_of_mul (by simpa using hdet)
    have hk11 : k.1 1 1 = a := by
      have : (k.1 1 1 - a) * g.1 1 0 = 0 := by linear_combination (-1 : F) * e10
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h10)
    have : g.1 1 1 * ((a : F)⁻¹ - a) = 0 := by linear_combination e11 + g.1 1 1 * hk11
    exact (mul_eq_zero.1 this).resolve_right hne
  · left
    have hk00 : k.1 0 0 = a := by
      have : (k.1 0 0 - a) * g.1 0 0 = 0 := by linear_combination (-1 : F) * e00
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h00)
    have h01 : g.1 0 1 = 0 := by
      have : g.1 0 1 * ((a : F)⁻¹ - a) = 0 := by linear_combination e01 + g.1 0 1 * hk00
      exact (mul_eq_zero.1 this).resolve_right hne
    refine ⟨h01, ?_⟩
    rw [h01] at hdet
    have h11 : g.1 1 1 ≠ 0 := right_ne_zero_of_mul (by simpa using hdet)
    have hk11 : k.1 1 1 = (a : F)⁻¹ := by
      have : (k.1 1 1 - (a : F)⁻¹) * g.1 1 1 = 0 := by linear_combination (-1 : F) * e11
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right h11)
    have : g.1 1 0 * ((a : F) - (a : F)⁻¹) = 0 := by linear_combination e10 + g.1 1 0 * hk11
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 ha)

theorem wGL_conj_mem_diagGL_iff (x : GL (Fin 2) F) :
    wGL F * x * (wGL F)⁻¹ ∈ diagGL F ↔ x ∈ diagGL F := by
  rw [mem_diagGL_iff, mem_diagGL_iff]
  simp only [mul_val_apply, wGL_inv_val]
  simp [and_comm]

theorem mul_wGL_inv_mem_diagGL {m : GL (Fin 2) F} (h00 : m.1 0 0 = 0) (h11 : m.1 1 1 = 0) :
    m * (wGL F)⁻¹ ∈ diagGL F := by
  rw [mem_diagGL_iff]
  simp only [mul_val_apply, wGL_inv_val]
  simp [h00, h11]

theorem wGL_sq : wGL F * wGL F = dg (-1) (-1) := by
  apply GL2_ext
  all_goals simp only [mul_val_apply, wGL_val, dg_val]
  all_goals simp

theorem wGL_sq_mem_diagGL : wGL F * wGL F ∈ diagGL F := by
  rw [wGL_sq]
  exact dg_mem_diagGL _ _

theorem bruhat_core {g : GL (Fin 2) F} (hc : g.1 1 0 ≠ 0) :
    ∃ s s' : F, ∃ m : GL (Fin 2) F, g = uT s * m * uT s' ∧ m.1 0 0 = 0 ∧ m.1 1 1 = 0 := by
  refine ⟨g.1 0 0 / g.1 1 0, g.1 1 1 / g.1 1 0,
    (uT (g.1 0 0 / g.1 1 0))⁻¹ * g * (uT (g.1 1 1 / g.1 1 0))⁻¹, by group, ?_, ?_⟩
  · simp only [mul_val_apply, uT_inv_val]
    simp
    field_simp
    ring
  · simp only [mul_val_apply, uT_inv_val]
    simp
    field_simp
    ring

theorem antidiag_four_not_upper {n : GL (Fin 2) F} (h00 : n.1 0 0 = 0) (h11 : n.1 1 1 = 0) :
    (n * uT 1 * n).1 1 0 ≠ 0 := by
  have hdet := det_ne_zero n
  rw [h00] at hdet
  have h10 : n.1 1 0 ≠ 0 := right_ne_zero_of_mul (by simpa using hdet)
  simp only [mul_val_apply, uT_val]
  simp [h00, h11, h10]

theorem four_identity {t : F} (ht : t ≠ 0) :
    wGL F * uT t * (wGL F)⁻¹ =
      uT (-t⁻¹) * dg (Units.mk0 t ht)⁻¹ (Units.mk0 t ht) * wGL F * uT (-t⁻¹) := by
  apply GL2_ext
  all_goals simp only [mul_val_apply, uT_val, wGL_val, wGL_inv_val, dg_val]
  all_goals simp
  all_goals field_simp
  all_goals ring

theorem upper_decomp_left {g : GL (Fin 2) F} (h10 : g.1 1 0 = 0) :
    uT (-(g.1 0 1 / g.1 1 1)) * g ∈ diagGL F := by
  have hdet := det_ne_zero g
  rw [h10] at hdet
  have h11 : g.1 1 1 ≠ 0 := right_ne_zero_of_mul (by simpa using hdet)
  rw [mem_diagGL_iff]
  simp only [mul_val_apply, uT_val]
  simp [h10]
  field_simp
  ring

theorem upper_decomp_right {g : GL (Fin 2) F} (h10 : g.1 1 0 = 0) :
    g * uT (-(g.1 0 1 / g.1 0 0)) ∈ diagGL F := by
  have hdet := det_ne_zero g
  rw [h10] at hdet
  have h00 : g.1 0 0 ≠ 0 := left_ne_zero_of_mul (by simpa using hdet)
  rw [mem_diagGL_iff]
  simp only [mul_val_apply, uT_val]
  simp [h10]
  field_simp
  ring

end CFSG.GH74.GLS.IVK.L2BN
