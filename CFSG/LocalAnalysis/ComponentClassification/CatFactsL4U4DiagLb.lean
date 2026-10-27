module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TBlocks
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Conj4

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace DiagL

open Matrix

variable {F : Type*} [Field F]

@[expose] def kZero (l : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, l, 0, 0; 1, 0, 0, 0; 0, 0, 0, l; 0, 0, 1, 0]

@[expose] def uK (l a b : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, a, b * l; 0, 1, b, a; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def lK (l a b : F) : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, 1, 0, 0; a, b * l, 1, 0; b, a, 0, 1]

@[expose] noncomputable def hK (l : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, l, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, l⁻¹, 0]

@[expose] def wK : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, -1, 0, 0]

theorem kZero_mul_kZero (l : F) : kZero l * kZero l = l • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kZero, Matrix.mul_apply, Fin.sum_univ_four]

theorem det_kZero (l : F) : (kZero l).det = l ^ 2 := by
  rw [kZero, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

theorem uK_comm (l a b : F) : uK l a b * kZero l = kZero l * uK l a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kZero, uK, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem lK_comm (l a b : F) : lK l a b * kZero l = kZero l * lK l a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kZero, lK, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem hK_comm {l : F} (hl : l ≠ 0) : hK l * kZero l = kZero l * hK l := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kZero, hK, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp

theorem det_uK (l a b : F) : (uK l a b).det = 1 := by
  rw [uK, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem det_lK (l a b : F) : (lK l a b).det = 1 := by
  rw [lK, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem det_hK {l : F} (hl : l ≠ 0) : (hK l).det = 1 := by
  rw [hK, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  field_simp

theorem det_wK : (wK : Matrix (Fin 4) (Fin 4) F).det = 1 := by
  rw [wK, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]

theorem uK_mul_uK (l a b c d : F) : uK l a b * uK l c d = uK l (a + c) (b + d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uK, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

theorem lK_mul_lK (l a b c d : F) : lK l a b * lK l c d = lK l (a + c) (b + d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lK, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem uK_zero (l : F) : uK l 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uK]

theorem lK_zero (l : F) : lK l 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lK]

@[expose] noncomputable def hKinv (l : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, 1, 0, 0; l⁻¹, 0, 0, 0; 0, 0, 0, l; 0, 0, 1, 0]

theorem hK_mul_hKinv {l : F} (hl : l ≠ 0) : hK l * hKinv l = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hK, hKinv, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp

theorem hK_conj_uK {l : F} (hl : l ≠ 0) (a b : F) :
    hK l * uK l a b * hKinv l = uK l (l * a) (l * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hK, hKinv, uK, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp

theorem hK_conj_lK {l : F} (hl : l ≠ 0) (a b : F) :
    hK l * lK l a b * hKinv l = lK l (l⁻¹ * a) (l⁻¹ * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hK, hKinv, lK, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp

theorem wK_eq (l : F) : (wK : Matrix (Fin 4) (Fin 4) F) = uK l 1 0 * lK l (-1) 0 * uK l 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wK, uK, lK, Matrix.mul_apply, Fin.sum_univ_four]

theorem wK_mul_wK : (wK : Matrix (Fin 4) (Fin 4) F) * wK = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wK, Matrix.mul_apply, Fin.sum_univ_four]

theorem sq_sub_mul_sq_ne_zero {l : F} (hns : ¬ IsSquare l) {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) :
    a ^ 2 - l * b ^ 2 ≠ 0 := by
  intro h0
  rcases eq_or_ne b 0 with hb | hb
  · rw [hb] at h0
    have : a = 0 := by simpa using h0
    rcases hab with ha | hb' <;> contradiction
  · apply hns
    refine ⟨a / b, ?_⟩
    field_simp
    linear_combination -h0

theorem eq_zero_of_smul_add_mulVec_eq_zero' {l : F} (hns : ¬ IsSquare l)
    {X : Matrix (Fin 4) (Fin 4) F} (hX : X * X = l • 1) {a b : F} {v : Fin 4 → F}
    (hv : a • v + b • (X *ᵥ v) = 0) (hab : a ≠ 0 ∨ b ≠ 0) : v = 0 := by
  have hsum : a ^ 2 - l * b ^ 2 ≠ 0 := sq_sub_mul_sq_ne_zero hns hab
  have hXX : ∀ w : Fin 4 → F, X *ᵥ (X *ᵥ w) = l • w := by
    intro w
    rw [Matrix.mulVec_mulVec, hX, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h1 : a • (a • v + b • (X *ᵥ v)) - b • (X *ᵥ (a • v + b • (X *ᵥ v))) =
      (a ^ 2 - l * b ^ 2) • v := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hXX]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hv, Matrix.mulVec_zero, smul_zero, smul_zero, sub_zero] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_left hsum

theorem exists_mul_eq_mul_kZero {l : F} (hns : ¬ IsSquare l) {X : Matrix (Fin 4) (Fin 4) F}
    (hX : X * X = l • 1) : ∃ P : Matrix (Fin 4) (Fin 4) F, IsUnit P.det ∧ X * P = P * kZero l := by
  classical
  have hXX : ∀ w : Fin 4 → F, X *ᵥ (X *ᵥ w) = l • w := by
    intro w
    rw [Matrix.mulVec_mulVec, hX, Matrix.smul_mulVec, Matrix.one_mulVec]
  set v₁ : Fin 4 → F := Pi.single 0 1 with hv₁
  have hv₁0 : v₁ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [hv₁] at this
  set W : Submodule F (Fin 4 → F) := Submodule.span F (Set.range ![v₁, X *ᵥ v₁]) with hW
  have hv₁W : v₁ ∈ W := Submodule.subset_span ⟨0, rfl⟩
  have hXv₁W : X *ᵥ v₁ ∈ W := Submodule.subset_span ⟨1, rfl⟩
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin 4, Pi.single i (1 : F) ∉ W := by
    by_contra hall
    push Not at hall
    have htop : W = ⊤ := by
      rw [eq_top_iff, ← (Pi.basisFun F (Fin 4)).span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simpa using hall i
    have h1 : Module.finrank F W ≤ 2 := by
      rw [hW]
      exact (finrank_range_le_card (R := F) ![v₁, X *ᵥ v₁]).trans (by simp)
    rw [htop, finrank_top, Module.finrank_fin_fun] at h1
    omega
  set v₂ : Fin 4 → F := Pi.single i₀ 1 with hv₂
  set col : Fin 4 → Fin 4 → F := ![v₁, X *ᵥ v₁, v₂, X *ᵥ v₂] with hcol
  set P : Matrix (Fin 4) (Fin 4) F := Matrix.of fun i j => col j i with hP
  refine ⟨P, ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • v₁ + g 1 • (X *ᵥ v₁) + (g 2 • v₂ + g 3 • (X *ᵥ v₂)) = 0 := by
      rw [← hg]
      ext i
      simp [Fin.sum_univ_four, hP, hcol]
      ring
    have hWX : ∀ w ∈ W, X *ᵥ w ∈ W := by
      intro w hw
      rw [hW] at hw ⊢
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      · rintro x ⟨j, rfl⟩
        fin_cases j
        · exact Submodule.subset_span ⟨1, rfl⟩
        · change X *ᵥ (X *ᵥ v₁) ∈ _
          rw [hXX]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
      · rw [Matrix.mulVec_zero]
        exact Submodule.zero_mem _
      · intro x y _ _ hx hy
        rw [Matrix.mulVec_add]
        exact Submodule.add_mem _ hx hy
      · intro c x _ hx
        rw [Matrix.mulVec_smul]
        exact Submodule.smul_mem _ c hx
    have hmem1 : g 0 • v₁ + g 1 • (X *ᵥ v₁) ∈ W :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ hv₁W) (Submodule.smul_mem _ _ hXv₁W)
    have h23 : g 2 = 0 ∧ g 3 = 0 := by
      by_contra hne
      have hne' : g 2 ≠ 0 ∨ g 3 ≠ 0 := by tauto
      have hu : g 2 • v₂ + g 3 • (X *ᵥ v₂) ∈ W := by
        have : g 2 • v₂ + g 3 • (X *ᵥ v₂) = -(g 0 • v₁ + g 1 • (X *ᵥ v₁)) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact hg'
        rw [this]
        exact Submodule.neg_mem _ hmem1
      have hsum : g 2 ^ 2 - l * g 3 ^ 2 ≠ 0 := sq_sub_mul_sq_ne_zero hns hne'
      have hv₂W : v₂ ∈ W := by
        have h1 : g 2 • (g 2 • v₂ + g 3 • (X *ᵥ v₂)) -
            g 3 • (X *ᵥ (g 2 • v₂ + g 3 • (X *ᵥ v₂))) = (g 2 ^ 2 - l * g 3 ^ 2) • v₂ := by
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hXX]
          ext i
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          ring
        have h2 : (g 2 ^ 2 - l * g 3 ^ 2) • v₂ ∈ W := by
          rw [← h1]
          exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hu)
            (Submodule.smul_mem _ _ (hWX _ hu))
        have := Submodule.smul_mem W (g 2 ^ 2 - l * g 3 ^ 2)⁻¹ h2
        rwa [smul_smul, inv_mul_cancel₀ hsum, one_smul] at this
      exact hi₀ hv₂W
    obtain ⟨h2, h3⟩ := h23
    rw [h2, h3, zero_smul, zero_smul, add_zero, add_zero] at hg'
    have h01 : g 0 = 0 ∧ g 1 = 0 := by
      by_contra hne
      have hne' : g 0 ≠ 0 ∨ g 1 ≠ 0 := by tauto
      exact hv₁0 (eq_zero_of_smul_add_mulVec_eq_zero' hns hX hg' hne')
    intro i
    fin_cases i
    · exact h01.1
    · exact h01.2
    · exact h2
    · exact h3
  · ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    change (X *ᵥ col j) i = _
    fin_cases j <;> simp [hcol, kZero, Fin.sum_univ_four, hP, hXX, mul_comm]

end DiagL

end CFSG.ComponentClassification.CatFactsL4U4
