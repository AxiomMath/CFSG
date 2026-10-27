module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Cover

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

open Matrix

variable {F : Type*} [Field F]

@[expose] def stdJ : Matrix (Fin 4) (Fin 4) F :=
  !![0, -1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, 1, 0]

@[expose] def stdD (a b : F) : Matrix (Fin 4) (Fin 4) F :=
  !![a, -b, 0, 0; b, a, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem stdD_mul_stdJ (a b : F) : stdD a b * stdJ = stdJ * stdD a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stdD, stdJ, Matrix.mul_apply, Fin.sum_univ_four]

theorem det_stdD (a b : F) : (stdD a b).det = a ^ 2 + b ^ 2 := by
  rw [stdD, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

theorem sq_add_sq_ne_zero (hns : ¬ IsSquare (-1 : F)) {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) :
    a ^ 2 + b ^ 2 ≠ 0 := by
  intro h0
  rcases eq_or_ne b 0 with hb | hb
  · rw [hb] at h0
    have : a = 0 := by simpa using h0
    rcases hab with ha | hb' <;> contradiction
  · apply hns
    refine ⟨a / b, ?_⟩
    field_simp
    linear_combination -h0

theorem eq_zero_of_smul_add_mulVec_eq_zero (hns : ¬ IsSquare (-1 : F))
    {X : Matrix (Fin 4) (Fin 4) F} (hX : X * X = -1) {a b : F} {v : Fin 4 → F}
    (hv : a • v + b • (X *ᵥ v) = 0) (hab : a ≠ 0 ∨ b ≠ 0) : v = 0 := by
  have hsum : a ^ 2 + b ^ 2 ≠ 0 := sq_add_sq_ne_zero hns hab
  have hXX : ∀ w : Fin 4 → F, X *ᵥ (X *ᵥ w) = -w := by
    intro w
    rw [Matrix.mulVec_mulVec, hX, Matrix.neg_mulVec, Matrix.one_mulVec]
  have h1 : a • (a • v + b • (X *ᵥ v)) - b • (X *ᵥ (a • v + b • (X *ᵥ v))) =
      (a ^ 2 + b ^ 2) • v := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hXX]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  rw [hv, Matrix.mulVec_zero, smul_zero, smul_zero, sub_zero] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_left hsum

theorem exists_mul_eq_mul_stdJ (hns : ¬ IsSquare (-1 : F)) {X : Matrix (Fin 4) (Fin 4) F}
    (hX : X * X = -1) : ∃ P : Matrix (Fin 4) (Fin 4) F, IsUnit P.det ∧ X * P = P * stdJ := by
  classical
  have hXX : ∀ w : Fin 4 → F, X *ᵥ (X *ᵥ w) = -w := by
    intro w
    rw [Matrix.mulVec_mulVec, hX, Matrix.neg_mulVec, Matrix.one_mulVec]
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
  have hPcol : ∀ j, (fun i => P i j) = col j := fun j => rfl
  refine ⟨P, ?_, ?_⟩
  ·
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
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
          exact Submodule.neg_mem _ (Submodule.subset_span ⟨0, rfl⟩)
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
      have hsum : g 2 ^ 2 + g 3 ^ 2 ≠ 0 := sq_add_sq_ne_zero hns hne'
      have hv₂W : v₂ ∈ W := by
        have h1 : g 2 • (g 2 • v₂ + g 3 • (X *ᵥ v₂)) -
            g 3 • (X *ᵥ (g 2 • v₂ + g 3 • (X *ᵥ v₂))) = (g 2 ^ 2 + g 3 ^ 2) • v₂ := by
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hXX]
          ext i
          simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
          ring
        have h2 : (g 2 ^ 2 + g 3 ^ 2) • v₂ ∈ W := by
          rw [← h1]
          exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hu)
            (Submodule.smul_mem _ _ (hWX _ hu))
        have := Submodule.smul_mem W (g 2 ^ 2 + g 3 ^ 2)⁻¹ h2
        rwa [smul_smul, inv_mul_cancel₀ hsum, one_smul] at this
      exact hi₀ hv₂W
    obtain ⟨h2, h3⟩ := h23
    rw [h2, h3, zero_smul, zero_smul, add_zero, add_zero] at hg'
    have h01 : g 0 = 0 ∧ g 1 = 0 := by
      by_contra hne
      have hne' : g 0 ≠ 0 ∨ g 1 ≠ 0 := by tauto
      exact hv₁0 (eq_zero_of_smul_add_mulVec_eq_zero hns hX hg' hne')
    intro i
    fin_cases i
    · exact h01.1
    · exact h01.2
    · exact h2
    · exact h3
  · ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    change (X *ᵥ col j) i = _
    fin_cases j <;> simp [hcol, stdJ, Fin.sum_univ_four, hP, hXX]

theorem exists_sq_add_sq' [Fintype F] (hF : Fintype.card F % 2 = 1) (x : F) :
    ∃ a c : F, a ^ 2 + c ^ 2 = x := by
  obtain ⟨a, c, h⟩ := FiniteField.exists_root_sum_quadratic (R := F)
    (f := Polynomial.X ^ 2) (g := Polynomial.X ^ 2 - Polynomial.C x)
    (Polynomial.degree_X_pow 2) (Polynomial.degree_X_pow_sub_C (by norm_num) x) hF
  refine ⟨a, c, ?_⟩
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C] at h
  linear_combination h

theorem exists_conj_of_sq_eq_neg_one [Fintype F] (hF : Fintype.card F % 2 = 1)
    (hns : ¬ IsSquare (-1 : F)) {X Y : Matrix (Fin 4) (Fin 4) F} (hX : X * X = -1)
    (hY : Y * Y = -1) : ∃ g : Matrix (Fin 4) (Fin 4) F, g.det = 1 ∧ g * X = Y * g := by
  obtain ⟨P, hP, hXP⟩ := exists_mul_eq_mul_stdJ hns hX
  obtain ⟨Q, hQ, hYQ⟩ := exists_mul_eq_mul_stdJ hns hY
  have h1 : P⁻¹ * X = stdJ * P⁻¹ := by
    calc P⁻¹ * X = P⁻¹ * X * (P * P⁻¹) := by rw [Matrix.mul_nonsing_inv _ hP, Matrix.mul_one]
      _ = P⁻¹ * (X * P) * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = P⁻¹ * (P * stdJ) * P⁻¹ := by rw [hXP]
      _ = stdJ * P⁻¹ := by rw [← Matrix.mul_assoc P⁻¹, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]
  set g₀ := Q * P⁻¹ with hg₀def
  have hg₀ : g₀ * X = Y * g₀ := by
    calc Q * P⁻¹ * X = Q * (P⁻¹ * X) := Matrix.mul_assoc _ _ _
      _ = Q * stdJ * P⁻¹ := by rw [h1, Matrix.mul_assoc]
      _ = Y * Q * P⁻¹ := by rw [← hYQ]
      _ = Y * (Q * P⁻¹) := Matrix.mul_assoc _ _ _
  have hPinv : P⁻¹.det = (P.det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hd : g₀.det ≠ 0 := by
    rw [hg₀def, Matrix.det_mul, hPinv]
    exact mul_ne_zero hQ.ne_zero (inv_ne_zero hP.ne_zero)
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq' hF (g₀.det)⁻¹
  set c := P * stdD a b * P⁻¹ with hc
  have hcX : c * X = X * c := by
    calc P * stdD a b * P⁻¹ * X = P * stdD a b * stdJ * P⁻¹ := by
          rw [Matrix.mul_assoc (P * stdD a b), h1, ← Matrix.mul_assoc]
      _ = P * stdJ * stdD a b * P⁻¹ := by
          rw [Matrix.mul_assoc P, stdD_mul_stdJ, ← Matrix.mul_assoc]
      _ = X * (P * stdD a b * P⁻¹) := by
          rw [← hXP]
          simp only [Matrix.mul_assoc]
  refine ⟨g₀ * c, ?_, ?_⟩
  · have hg₀d : g₀.det = Q.det * (P.det)⁻¹ := by rw [hg₀def, Matrix.det_mul, hPinv]
    rw [Matrix.det_mul, hc]
    simp only [Matrix.det_mul]
    rw [det_stdD, hab, hPinv, hg₀d]
    have hQ0 := hQ.ne_zero
    have hP0 := hP.ne_zero
    field_simp
  · rw [Matrix.mul_assoc, hcX, ← Matrix.mul_assoc, hg₀, Matrix.mul_assoc]

end CFSG.ComponentClassification.CatFactsL4U4
