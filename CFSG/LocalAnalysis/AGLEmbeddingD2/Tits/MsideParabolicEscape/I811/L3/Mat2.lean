module

public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

open Matrix

variable {F : Type} [Field F]

@[expose] def cMat : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, -1]

theorem cMat_relation : (cMat : Matrix (Fin 2) (Fin 2) F) * cMat + cMat + 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cMat]

theorem cMat_transpose_relation :
    (cMat : Matrix (Fin 2) (Fin 2) F)ᵀ * cMatᵀ + cMatᵀ + 1 = 0 := by
  rw [← Matrix.transpose_mul, ← Matrix.transpose_add, ← Matrix.transpose_one,
    ← Matrix.transpose_add, cMat_relation, Matrix.transpose_zero]

theorem cMat_det : (cMat : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  simp [cMat, Matrix.det_fin_two]

@[expose] def pairMat (D : Matrix (Fin 2) (Fin 2) F) (s : Fin 2 → F) :
    Matrix (Fin 2) (Fin 2) F :=
  !![s 0, (D *ᵥ s) 0; s 1, (D *ᵥ s) 1]

theorem pairMat_mulVec_e0 (D : Matrix (Fin 2) (Fin 2) F) (s : Fin 2 → F) :
    pairMat D s *ᵥ ![1, 0] = s := by
  funext i
  fin_cases i <;> simp [pairMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

variable {D : Matrix (Fin 2) (Fin 2) F}

theorem mulVec_mulVec_of_relation (hD : D * D + D + 1 = 0) (s : Fin 2 → F) :
    D *ᵥ (D *ᵥ s) = -(D *ᵥ s) - s := by
  have h : D * D = -D - 1 := by
    rw [← sub_eq_zero]
    rw [← hD]
    abel
  rw [Matrix.mulVec_mulVec, h, Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec]

theorem mulVec_ne_smul (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0) (hD : D * D + D + 1 = 0)
    {s : Fin 2 → F} (hs : s ≠ 0) (μ : F) : D *ᵥ s ≠ μ • s := by
  intro h
  have h2 := mulVec_mulVec_of_relation hD s
  rw [h, Matrix.mulVec_smul, h] at h2
  have h3 : (μ ^ 2 + μ + 1) • s = 0 := by
    rw [add_smul, add_smul, one_smul, pow_two, mul_smul]
    rw [h2]
    abel
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact hroot μ h4
  · exact hs h4

theorem pairMat_det_ne_zero (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0) (hD : D * D + D + 1 = 0)
    {s : Fin 2 → F} (hs : s ≠ 0) : (pairMat D s).det ≠ 0 := by
  intro hdet
  rw [pairMat, Matrix.det_fin_two_of] at hdet
  by_cases h0 : s 0 = 0
  · have h1 : s 1 ≠ 0 := by
      intro h1
      apply hs
      funext i
      fin_cases i
      · exact h0
      · exact h1
    have hD0 : (D *ᵥ s) 0 = 0 := by
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at hdet
      exact (mul_eq_zero.mp hdet).resolve_right h1
    refine mulVec_ne_smul hroot hD hs ((D *ᵥ s) 1 / s 1) ?_
    funext i
    fin_cases i
    · simp [hD0, h0]
    · simp [div_mul_cancel₀ _ h1]
  · refine mulVec_ne_smul hroot hD hs ((D *ᵥ s) 0 / s 0) ?_
    funext i
    fin_cases i
    · simp [div_mul_cancel₀ _ h0]
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.mk_one, Fin.isValue]
      field_simp
      linear_combination hdet

theorem pairMat_mul_cMat (hD : D * D + D + 1 = 0) (s : Fin 2 → F) :
    pairMat D s * cMat = D * pairMat D s := by
  have h2 := mulVec_mulVec_of_relation hD s
  have e0 := congrFun h2 0
  have e1 := congrFun h2 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairMat, cMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct] at e0 e1 ⊢
  all_goals first | ring1 | linear_combination -e0 | linear_combination -e1

@[expose] noncomputable def pairGL (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0) (hD : D * D + D + 1 = 0)
    {s : Fin 2 → F} (hs : s ≠ 0) : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero (pairMat D s) (pairMat_det_ne_zero hroot hD hs)

theorem exists_comm_mulVec_eq (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0) (hD : D * D + D + 1 = 0)
    {s t : Fin 2 → F} (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ Z : GL (Fin 2) F, (Z : Matrix (Fin 2) (Fin 2) F) * D = D * Z ∧
      (Z : Matrix (Fin 2) (Fin 2) F) *ᵥ s = t := by
  set P := pairGL hroot hD hs
  set P' := pairGL hroot hD ht
  refine ⟨P' * P⁻¹, ?_, ?_⟩
  · have hP : (P : Matrix (Fin 2) (Fin 2) F) * cMat = D * (P : Matrix (Fin 2) (Fin 2) F) :=
      pairMat_mul_cMat hD s
    have hP' : (P' : Matrix (Fin 2) (Fin 2) F) * cMat = D * (P' : Matrix (Fin 2) (Fin 2) F) :=
      pairMat_mul_cMat hD t
    have hPi : ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * D =
        cMat * ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      have h1 : ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (P : Matrix _ _ F) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have h2 : (P : Matrix (Fin 2) (Fin 2) F) * ((P⁻¹ : GL (Fin 2) F) : Matrix _ _ F) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * D
          = ((P⁻¹ : GL (Fin 2) F) : Matrix _ _ F) * D * ((P : Matrix _ _ F) *
              ((P⁻¹ : GL (Fin 2) F) : Matrix _ _ F)) := by rw [h2, Matrix.mul_one]
        _ = ((P⁻¹ : GL (Fin 2) F) : Matrix _ _ F) * (D * (P : Matrix (Fin 2) (Fin 2) F)) *
              ((P⁻¹ : GL (Fin 2) F) : Matrix _ _ F) := by
            simp only [Matrix.mul_assoc]
        _ = ((P⁻¹ : GL (Fin 2) F) : Matrix _ _ F) * ((P : Matrix _ _ F) * cMat) *
              ((P⁻¹ : GL (Fin 2) F) : Matrix _ _ F) := by rw [hP]
        _ = cMat * ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
            rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Units.val_mul, Matrix.mul_assoc, hPi, ← Matrix.mul_assoc, hP', Matrix.mul_assoc]
  · have hPs : (P : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] = s := pairMat_mulVec_e0 D s
    have hP't : (P' : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] = t := pairMat_mulVec_e0 D t
    have h1 : ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (P : Matrix _ _ F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [← hPs, Matrix.mulVec_mulVec, Units.val_mul, Matrix.mul_assoc, h1, Matrix.mul_one, hP't]

theorem eq_smul_one_of_comm_of_mulVec_eq (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0)
    (hD : D * D + D + 1 = 0) {Z : Matrix (Fin 2) (Fin 2) F} (hZ : Z * D = D * Z)
    {s : Fin 2 → F} (hs : s ≠ 0) {μ : F} (hZs : Z *ᵥ s = μ • s) : Z = μ • 1 := by
  set M := Z - μ • (1 : Matrix (Fin 2) (Fin 2) F)
  have hMs : M *ᵥ s = 0 := by
    simp only [M, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hZs, sub_self]
  have hMD : M *ᵥ (D *ᵥ s) = 0 := by
    have : M * D = D * M := by
      simp only [M, Matrix.sub_mul, Matrix.mul_sub, hZ, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mulVec_mulVec, this, ← Matrix.mulVec_mulVec, hMs, Matrix.mulVec_zero]
  have hMP : M * pairMat D s = 0 := by
    ext i j
    fin_cases j
    · have h := congrFun hMs i
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.zero_apply] at h
      simp only [pairMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply]
      simpa using h
    · have h := congrFun hMD i
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.zero_apply] at h
      simp only [pairMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply]
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  have hdet := pairMat_det_ne_zero hroot hD hs
  have hunit : IsUnit (pairMat D s).det := isUnit_iff_ne_zero.mpr hdet
  have hM : M = 0 := by
    calc M = M * (pairMat D s * (pairMat D s)⁻¹) := by rw [Matrix.mul_nonsing_inv _ hunit,
          Matrix.mul_one]
      _ = 0 := by rw [← Matrix.mul_assoc, hMP, Matrix.zero_mul]
  exact sub_eq_zero.mp hM

theorem pairMat_cMat_det (s : Fin 2 → F) :
    (pairMat cMat s).det = s 0 ^ 2 - s 0 * s 1 + s 1 ^ 2 := by
  simp [pairMat, cMat, Matrix.det_fin_two_of, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem exists_pairMat_det_eq [Fintype F] (h3 : (3 : F) ≠ 0) {μ : F} (hμ : μ ≠ 0) :
    ∃ s : Fin 2 → F, s ≠ 0 ∧ (pairMat cMat s).det = μ := by
  by_cases h2 : ringChar F = 2
  · obtain ⟨a, ha⟩ := FiniteField.isSquare_of_char_two h2 μ
    refine ⟨![a, 0], ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp only [Matrix.cons_val_zero, Pi.zero_apply] at this
      rw [this, mul_zero] at ha
      exact hμ ha
    · rw [pairMat_cMat_det]
      simp [ha, pow_two]
  · have hodd : Fintype.card F % 2 = 1 := FiniteField.odd_card_of_char_ne_two h2
    have hf : (Polynomial.X ^ 2 : Polynomial F).degree = 2 := by
      rw [Polynomial.degree_X_pow]
      rfl
    have hg : (Polynomial.C (3 : F) * Polynomial.X ^ 2 - Polynomial.C μ).degree = 2 := by
      rw [Polynomial.degree_sub_C, Polynomial.degree_C_mul_X_pow 2 h3]
      · rfl
      · rw [Polynomial.degree_C_mul_X_pow 2 h3]
        exact compareOfLessAndEq_eq_lt.mp rfl
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
    simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C] at hab
    have hdet : (pairMat cMat ![a + b, 2 * b]).det = μ := by
      rw [pairMat_cMat_det]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination hab
    refine ⟨![a + b, 2 * b], ?_, hdet⟩
    intro h
    rw [h] at hdet
    simp [pairMat_cMat_det] at hdet
    exact hμ hdet.symm

theorem comm_cMat_entries {Z : Matrix (Fin 2) (Fin 2) F} (hZ : Z * cMat = cMat * Z) :
    Z 0 1 = -Z 1 0 ∧ Z 1 1 = Z 0 0 - Z 1 0 := by
  have h01 := congrFun (congrFun hZ 0) 0
  have h02 := congrFun (congrFun hZ 0) 1
  simp [cMat, Matrix.mul_apply, Fin.sum_univ_two] at h01 h02
  constructor
  · linear_combination h01
  · linear_combination h02 + h01

theorem comm_of_comm_cMat {X Y : Matrix (Fin 2) (Fin 2) F} (hX : X * cMat = cMat * X)
    (hY : Y * cMat = cMat * Y) : X * Y = Y * X := by
  obtain ⟨hx1, hx2⟩ := comm_cMat_entries hX
  obtain ⟨hy1, hy2⟩ := comm_cMat_entries hY
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hx1, hx2, hy1, hy2] <;>
    ring

theorem exists_comm_det_smul_mulVec_eq (hroot : ∀ x : F, x ^ 2 + x + 1 ≠ 0)
    (hcube : ∀ x : F, ∃ y : F, y ^ 3 = x) (hD : D * D + D + 1 = 0) {s t : Fin 2 → F}
    (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ Z : GL (Fin 2) F, (Z : Matrix (Fin 2) (Fin 2) F) * D = D * Z ∧
      (Z : Matrix (Fin 2) (Fin 2) F).det • ((Z : Matrix (Fin 2) (Fin 2) F) *ᵥ s) = t := by
  obtain ⟨Z₀, hZ₀D, hZ₀s⟩ := exists_comm_mulVec_eq hroot hD hs ht
  have hdet₀ : (Z₀ : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← isUnit_iff_ne_zero]
    exact Matrix.isUnit_det_of_invertible _
  obtain ⟨μ, hμ⟩ := hcube ((Z₀ : Matrix (Fin 2) (Fin 2) F).det)⁻¹
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hμ
    exact hdet₀ (inv_eq_zero.mp hμ.symm)
  refine ⟨Units.mk0 μ hμ0 • Z₀, ?_, ?_⟩
  · rw [show ((Units.mk0 μ hμ0 • Z₀ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      μ • (Z₀ : Matrix (Fin 2) (Fin 2) F) from rfl]
    rw [Matrix.smul_mul, Matrix.mul_smul, hZ₀D]
  · rw [show ((Units.mk0 μ hμ0 • Z₀ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      μ • (Z₀ : Matrix (Fin 2) (Fin 2) F) from rfl]
    rw [Matrix.det_smul, Matrix.smul_mulVec, hZ₀s, Fintype.card_fin, smul_smul]
    have : μ ^ 2 * (Z₀ : Matrix (Fin 2) (Fin 2) F).det * μ = 1 := by
      calc μ ^ 2 * (Z₀ : Matrix (Fin 2) (Fin 2) F).det * μ
          = μ ^ 3 * (Z₀ : Matrix (Fin 2) (Fin 2) F).det := by ring
        _ = 1 := by rw [hμ, inv_mul_cancel₀ hdet₀]
    rw [this, one_smul]

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3
