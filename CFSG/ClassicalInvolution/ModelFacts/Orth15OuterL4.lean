module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4Mat
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.ClassicalInvolution.Models.LinearFrames.Frame

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def u01 (t : F) : SL(4, F) :=
  ⟨E01 t, by simp [E01, Matrix.det_succ_row_zero, Fin.sum_univ_succ]⟩
@[expose] def u10 (t : F) : SL(4, F) :=
  ⟨E10 t, by simp [E10, Matrix.det_succ_row_zero, Fin.sum_univ_succ]⟩
@[expose] def u23 (t : F) : SL(4, F) :=
  ⟨E23 t, by simp [E23, Matrix.det_succ_row_zero, Fin.sum_univ_succ]⟩
@[expose] def u32 (t : F) : SL(4, F) :=
  ⟨E32 t, by simp [E32, Matrix.det_succ_row_zero, Fin.sum_univ_succ]⟩
@[expose] def u02 (t : F) : SL(4, F) :=
  ⟨!![1, 0, t, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
    by simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]⟩

theorem blockMat_four_zero (A : Matrix (Fin 2) (Fin 2) F) :
    CFSG.ClassicalInvolution.Phan.blockMat 4 0 A =
      !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext a b
  rw [CFSG.ClassicalInvolution.Phan.blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem blockMat_four_two (A : Matrix (Fin 2) (Fin 2) F) :
    CFSG.ClassicalInvolution.Phan.blockMat 4 2 A =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, A 0 0, A 0 1; 0, 0, A 1 0, A 1 1] := by
  ext a b
  rw [CFSG.ClassicalInvolution.Phan.blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem u01_mem (t : F) : u01 t ∈ (blockSL F 4 2 0 (by norm_num)).range := by
  let A : SL(2, F) := ⟨!![1, t; 0, 1], by simp⟩
  refine ⟨A, Subtype.ext ?_⟩
  rw [coe_blockSL, blockMat_four_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u01, E01, A]

theorem u10_mem (t : F) : u10 t ∈ (blockSL F 4 2 0 (by norm_num)).range := by
  let A : SL(2, F) := ⟨!![1, 0; t, 1], by simp⟩
  refine ⟨A, Subtype.ext ?_⟩
  rw [coe_blockSL, blockMat_four_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u10, E10, A]

theorem u23_mem (t : F) : u23 t ∈ (blockSL F 4 2 2 (by norm_num)).range := by
  let A : SL(2, F) := ⟨!![1, t; 0, 1], by simp⟩
  refine ⟨A, Subtype.ext ?_⟩
  rw [coe_blockSL, blockMat_four_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u23, E23, A]

theorem u32_mem (t : F) : u32 t ∈ (blockSL F 4 2 2 (by norm_num)).range := by
  let A : SL(2, F) := ⟨!![1, 0; t, 1], by simp⟩
  refine ⟨A, Subtype.ext ?_⟩
  rw [coe_blockSL, blockMat_four_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u32, E32, A]

theorem alpha_proj_zero {n : ℕ} (A : GL (Fin n) F) (σ : F ≃+* F) (g : SL(n, F)) :
    (conjAut n F A * fieldAut n F σ) (proj n F g) =
      proj n F (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A
        (Matrix.SpecialLinearGroup.map σ.toRingHom g)) := by
  show conjAut n F A (fieldAut n F σ (proj n F g)) = _
  rw [fieldAut_proj, conjAut_proj]

theorem alpha_proj_one {n : ℕ} (A : GL (Fin n) F) (σ : F ≃+* F) (g : SL(n, F)) :
    (conjAut n F A * fieldAut n F σ * dualAut n F) (proj n F g) =
      proj n F (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n F A
        (Matrix.SpecialLinearGroup.map σ.toRingHom (g⁻¹).transpose)) := by
  show conjAut n F A (fieldAut n F σ (dualAut n F (proj n F g))) = _
  rw [dualAut_proj, fieldAut_proj, conjAut_proj]

theorem proj_eq_exists {n : ℕ} {a b : SL(n, F)} (h : proj n F a = proj n F b) :
    ∃ c : Fˣ, c ^ n = 1 ∧
      (b : Matrix (Fin n) (Fin n) F) = (c : F) • (a : Matrix (Fin n) (Fin n) F) := by
  have h1 : a⁻¹ * b ∈ scalars n F := QuotientGroup.eq.mp h
  obtain ⟨c, hc, hcm⟩ := mem_scalars.mp h1
  refine ⟨c, hc, ?_⟩
  have hb : a * (a⁻¹ * b) = b := by group
  have : (b : Matrix (Fin n) (Fin n) F) = (a : Matrix (Fin n) (Fin n) F) *
      ((a⁻¹ * b : SL(n, F)) : Matrix (Fin n) (Fin n) F) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hb]
  rw [this, hcm, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
    Matrix.mul_one]

theorem trace_E01 (t : F) : (E01 t).trace = 4 := by
  simp [E01, Matrix.trace, Fin.sum_univ_four]; norm_num

theorem u01_mul_neg (t : F) : u01 t * u01 (-t) = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u01, E01, Matrix.mul_apply, Fin.sum_univ_four]

theorem u10_mul_neg (t : F) : u10 t * u10 (-t) = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u10, E10, Matrix.mul_apply, Fin.sum_univ_four]

theorem u23_mul_neg (t : F) : u23 t * u23 (-t) = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u23, E23, Matrix.mul_apply, Fin.sum_univ_four]

theorem u32_mul_neg (t : F) : u32 t * u32 (-t) = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u32, E32, Matrix.mul_apply, Fin.sum_univ_four]

theorem coe_inv_transpose_u01 (t : F) :
    (((u01 t)⁻¹).transpose : Matrix (Fin 4) (Fin 4) F) = E10 (-t) := by
  rw [inv_eq_of_mul_eq_one_right (u01_mul_neg t), Matrix.SpecialLinearGroup.coe_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u01, E01, E10]

theorem coe_inv_transpose_u10 (t : F) :
    (((u10 t)⁻¹).transpose : Matrix (Fin 4) (Fin 4) F) = E01 (-t) := by
  rw [inv_eq_of_mul_eq_one_right (u10_mul_neg t), Matrix.SpecialLinearGroup.coe_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u10, E10, E01]

theorem coe_inv_transpose_u23 (t : F) :
    (((u23 t)⁻¹).transpose : Matrix (Fin 4) (Fin 4) F) = E32 (-t) := by
  rw [inv_eq_of_mul_eq_one_right (u23_mul_neg t), Matrix.SpecialLinearGroup.coe_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u23, E23, E32]

theorem coe_inv_transpose_u32 (t : F) :
    (((u32 t)⁻¹).transpose : Matrix (Fin 4) (Fin 4) F) = E23 (-t) := by
  rw [inv_eq_of_mul_eq_one_right (u32_mul_neg t), Matrix.SpecialLinearGroup.coe_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u32, E32, E23]

theorem trace_conj {n : ℕ} (A : GL (Fin n) F) (X : Matrix (Fin n) (Fin n) F) :
    ((A : Matrix (Fin n) (Fin n) F) * X * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)).trace =
      X.trace := by
  have hNA : ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) =
      1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [Matrix.trace_mul_comm ((A : Matrix (Fin n) (Fin n) F) * X), ← Matrix.mul_assoc, hNA,
    Matrix.one_mul]

theorem exact_rel_zero (h4 : (4 : F) ≠ 0) (A : GL (Fin 4) F) (σ : F ≃+* F) {r : SL(4, F)}
    (hr : (conjAut 4 F A * fieldAut 4 F σ) (proj 4 F r) = proj 4 F r)
    (htr : (r : Matrix (Fin 4) (Fin 4) F).trace = 4)
    (htrσ : ((r : Matrix (Fin 4) (Fin 4) F).map σ).trace = 4) :
    (r : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) =
      (A : Matrix (Fin 4) (Fin 4) F) * (r : Matrix (Fin 4) (Fin 4) F).map σ := by
  rw [alpha_proj_zero] at hr
  obtain ⟨c, hc, hcm⟩ := proj_eq_exists hr
  have h1 : ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F A
      (Matrix.SpecialLinearGroup.map σ.toRingHom r) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      (A : Matrix (Fin 4) (Fin 4) F) * (r : Matrix (Fin 4) (Fin 4) F).map σ *
        ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix]
    rfl
  have hNA : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (A : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [h1] at hcm
  have htrace := congrArg Matrix.trace hcm
  rw [Matrix.trace_smul, trace_conj, htrσ, htr, smul_eq_mul] at htrace
  have hc1 : (c : F) = 1 := by
    have : (4 : F) * (1 - (c : F)) = 0 := by linear_combination htrace
    have := (mul_eq_zero.mp this).resolve_left h4
    linear_combination -this
  rw [hc1, one_smul] at hcm
  calc (r : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F)
      = ((A : Matrix (Fin 4) (Fin 4) F) * (r : Matrix (Fin 4) (Fin 4) F).map σ *
          ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * (A : Matrix (Fin 4) (Fin 4) F) := by
        rw [← hcm]
    _ = (A : Matrix (Fin 4) (Fin 4) F) * (r : Matrix (Fin 4) (Fin 4) F).map σ := by
        rw [Matrix.mul_assoc, hNA, Matrix.mul_one]

theorem exact_rel_one (h4 : (4 : F) ≠ 0) (A : GL (Fin 4) F) (σ : F ≃+* F) {r : SL(4, F)}
    (hr : (conjAut 4 F A * fieldAut 4 F σ * dualAut 4 F) (proj 4 F r) = proj 4 F r)
    (htr : (r : Matrix (Fin 4) (Fin 4) F).trace = 4)
    (htrσ : ((((r⁻¹).transpose : SL(4, F)) : Matrix (Fin 4) (Fin 4) F).map σ).trace = 4) :
    (r : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) =
      (A : Matrix (Fin 4) (Fin 4) F) *
        ((((r⁻¹).transpose : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)).map σ := by
  rw [alpha_proj_one] at hr
  obtain ⟨c, hc, hcm⟩ := proj_eq_exists hr
  have h1 : ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F A
      (Matrix.SpecialLinearGroup.map σ.toRingHom (r⁻¹).transpose) : SL(4, F)) :
        Matrix (Fin 4) (Fin 4) F) =
      (A : Matrix (Fin 4) (Fin 4) F) *
        ((((r⁻¹).transpose : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)).map σ *
        ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix]
    rfl
  have hNA : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (A : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [h1] at hcm
  have htrace := congrArg Matrix.trace hcm
  rw [Matrix.trace_smul, trace_conj, htrσ, htr, smul_eq_mul] at htrace
  have hc1 : (c : F) = 1 := by
    have : (4 : F) * (1 - (c : F)) = 0 := by linear_combination htrace
    have := (mul_eq_zero.mp this).resolve_left h4
    linear_combination -this
  rw [hc1, one_smul] at hcm
  calc (r : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F)
      = ((A : Matrix (Fin 4) (Fin 4) F) *
          ((((r⁻¹).transpose : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)).map σ *
          ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * (A : Matrix (Fin 4) (Fin 4) F) := by
        rw [← hcm]
    _ = (A : Matrix (Fin 4) (Fin 4) F) *
        ((((r⁻¹).transpose : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)).map σ := by
        rw [Matrix.mul_assoc, hNA, Matrix.mul_one]

theorem map_E01 (σ : F ≃+* F) (t : F) : (E01 t).map σ = E01 (σ t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E01]

theorem map_E10 (σ : F ≃+* F) (t : F) : (E10 t).map σ = E10 (σ t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E10]

theorem map_E23 (σ : F ≃+* F) (t : F) : (E23 t).map σ = E23 (σ t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E23]

theorem map_E32 (σ : F ≃+* F) (t : F) : (E32 t).map σ = E32 (σ t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E32]

theorem trace_E10 (t : F) : (E10 t).trace = 4 := by
  simp [E10, Matrix.trace, Fin.sum_univ_four]; norm_num

theorem trace_E23 (t : F) : (E23 t).trace = 4 := by
  simp [E23, Matrix.trace, Fin.sum_univ_four]; norm_num

theorem trace_E32 (t : F) : (E32 t).trace = 4 := by
  simp [E32, Matrix.trace, Fin.sum_univ_four]; norm_num

theorem four_ne_zero (h2 : (2 : F) ≠ 0) : (4 : F) ≠ 0 := by
  have : (4 : F) = 2 * 2 := by norm_num
  rw [this]
  exact mul_ne_zero h2 h2

theorem det_ne_zero (A : GL (Fin 4) F) : (A : Matrix (Fin 4) (Fin 4) F).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero

theorem aut_fix_blocks_zero (h2 : (2 : F) ≠ 0) (A : GL (Fin 4) F) (σ : F ≃+* F)
    (hfix : ∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range,
      (conjAut 4 F A * fieldAut 4 F σ) (proj 4 F r) = proj 4 F r)
    (hfix' : ∀ r ∈ (blockSL F 4 2 2 (by norm_num)).range,
      (conjAut 4 F A * fieldAut 4 F σ) (proj 4 F r) = proj 4 F r) :
    σ = RingEquiv.refl F ∧ ∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧
      (A : Matrix (Fin 4) (Fin 4) F) = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b] := by
  have h4 := four_ne_zero h2
  refine diag_of_rel_zero σ (A : Matrix (Fin 4) (Fin 4) F) (det_ne_zero A) ?_ ?_ ?_ ?_ <;>
    intro t
  · have := exact_rel_zero h4 A σ (hfix _ (u01_mem t)) (trace_E01 t)
      (by rw [show ((u01 t : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = E01 t from rfl, map_E01,
        trace_E01])
    rwa [show ((u01 t : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = E01 t from rfl, map_E01] at this
  · have := exact_rel_zero h4 A σ (hfix _ (u10_mem t)) (trace_E10 t)
      (by rw [show ((u10 t : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = E10 t from rfl, map_E10,
        trace_E10])
    rwa [show ((u10 t : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = E10 t from rfl, map_E10] at this
  · have := exact_rel_zero h4 A σ (hfix' _ (u23_mem t)) (trace_E23 t)
      (by rw [show ((u23 t : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = E23 t from rfl, map_E23,
        trace_E23])
    rwa [show ((u23 t : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = E23 t from rfl, map_E23] at this
  · have := exact_rel_zero h4 A σ (hfix' _ (u32_mem t)) (trace_E32 t)
      (by rw [show ((u32 t : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = E32 t from rfl, map_E32,
        trace_E32])
    rwa [show ((u32 t : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = E32 t from rfl, map_E32] at this

theorem aut_fix_blocks_one (h2 : (2 : F) ≠ 0) (A : GL (Fin 4) F) (σ : F ≃+* F)
    (hfix : ∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range,
      (conjAut 4 F A * fieldAut 4 F σ * dualAut 4 F) (proj 4 F r) = proj 4 F r)
    (hfix' : ∀ r ∈ (blockSL F 4 2 2 (by norm_num)).range,
      (conjAut 4 F A * fieldAut 4 F σ * dualAut 4 F) (proj 4 F r) = proj 4 F r) :
    σ = RingEquiv.refl F ∧ ∃ m n : F, m ≠ 0 ∧ n ≠ 0 ∧
      (A : Matrix (Fin 4) (Fin 4) F) =
        !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] := by
  have h4 := four_ne_zero h2
  refine antidiag_of_rel_one σ (A : Matrix (Fin 4) (Fin 4) F) (det_ne_zero A) ?_ ?_ ?_ ?_ <;>
    intro t
  · have := exact_rel_one h4 A σ (hfix _ (u01_mem t)) (trace_E01 t)
      (by rw [coe_inv_transpose_u01, map_E10, trace_E10])
    rwa [show ((u01 t : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = E01 t from rfl,
      coe_inv_transpose_u01, map_E10, map_neg] at this
  · have := exact_rel_one h4 A σ (hfix _ (u10_mem t)) (trace_E10 t)
      (by rw [coe_inv_transpose_u10, map_E01, trace_E01])
    rwa [show ((u10 t : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = E10 t from rfl,
      coe_inv_transpose_u10, map_E01, map_neg] at this
  · have := exact_rel_one h4 A σ (hfix' _ (u23_mem t)) (trace_E23 t)
      (by rw [coe_inv_transpose_u23, map_E32, trace_E32])
    rwa [show ((u23 t : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = E23 t from rfl,
      coe_inv_transpose_u23, map_E32, map_neg] at this
  · have := exact_rel_one h4 A σ (hfix' _ (u32_mem t)) (trace_E32 t)
      (by rw [coe_inv_transpose_u32, map_E23, trace_E23])
    rwa [show ((u32 t : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = E32 t from rfl,
      coe_inv_transpose_u32, map_E23, map_neg] at this

theorem exact_rel_conj (h4 : (4 : F) ≠ 0) (g : GL (Fin 4) F) {r : SL(4, F)}
    (hr : conjAut 4 F g (proj 4 F r) = proj 4 F r)
    (htr : (r : Matrix (Fin 4) (Fin 4) F).trace = 4) :
    (r : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) =
      (g : Matrix (Fin 4) (Fin 4) F) * (r : Matrix (Fin 4) (Fin 4) F) := by
  have := exact_rel_zero h4 g (RingEquiv.refl F) (r := r)
    (by rw [show fieldAut 4 F (RingEquiv.refl F) = 1 from map_one _, mul_one]; exact hr) htr
    (by simpa using htr)
  simpa using this

theorem trace_u02 (t : F) : (((u02 t : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)).trace = 4 := by
  simp [u02, Matrix.trace, Fin.sum_univ_four]; norm_num

theorem conjAut_eq_of_smul (A B : GL (Fin 4) F) (c : F) (hc : c ≠ 0)
    (h : (A : Matrix (Fin 4) (Fin 4) F) = c • (B : Matrix (Fin 4) (Fin 4) F)) :
    conjAut 4 F A = conjAut 4 F B := by
  have hNA : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      c⁻¹ • ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    have hAN : (A : Matrix (Fin 4) (Fin 4) F) *
        ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hNB : ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (B : Matrix (Fin 4) (Fin 4) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [h, Matrix.smul_mul] at hAN
    calc ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
        = c⁻¹ • (((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            (c • ((B : Matrix (Fin 4) (Fin 4) F) *
              ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)))) := by
          rw [← Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, ← Matrix.mul_assoc,
            hNB, Matrix.one_mul]
      _ = c⁻¹ • ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
          rw [hAN, Matrix.mul_one]
  ext p
  obtain ⟨s, rfl⟩ := proj_surjective 4 F p
  rw [conjAut_proj, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_slConjugation, hNA, h]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem conjAut_toGL (g : SL(4, F)) :
    conjAut 4 F (Matrix.SpecialLinearGroup.toGL g) = MulAut.conj (proj 4 F g) := by
  ext p
  obtain ⟨s, rfl⟩ := proj_surjective 4 F p
  rw [conjAut_proj]
  show _ = proj 4 F g * proj 4 F s * (proj 4 F g)⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  congr 1

theorem negBlock_four : negBlock F 4 0 = !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  rw [negBlock_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_toGL_rootInv :
    ((Matrix.SpecialLinearGroup.toGL (rootInv F (show 2 ≤ 4 by norm_num)) : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_rootInv, negBlock_four]

theorem sq_of_diag (h2 : (2 : F) ≠ 0) (A : GL (Fin 4) F) (a b : F) (ha : a ≠ 0)
    (hM : (A : Matrix (Fin 4) (Fin 4) F) = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b])
    (h4 : conjAut 4 F A * conjAut 4 F A * (conjAut 4 F A * conjAut 4 F A) = 1) :
    conjAut 4 F A * conjAut 4 F A = 1 ∨
      conjAut 4 F A * conjAut 4 F A =
        MulAut.conj (proj 4 F (rootInv F (show 2 ≤ 4 by norm_num))) := by
  have h4' := four_ne_zero h2
  have hD : conjAut 4 F A * conjAut 4 F A = conjAut 4 F (A * A) := (map_mul _ _ _).symm
  rw [hD] at h4 ⊢
  have hDD : conjAut 4 F (A * A * (A * A)) = 1 := by rw [map_mul]; exact h4
  have hrel := exact_rel_conj h4' (A * A * (A * A)) (r := u02 1) (by rw [hDD]; rfl) (trace_u02 1)
  have hMM : ((A * A * (A * A) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      !![a ^ 4, 0, 0, 0; 0, a ^ 4, 0, 0; 0, 0, b ^ 4, 0; 0, 0, 0, b ^ 4] := by
    simp only [Units.val_mul, hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  rw [hMM] at hrel
  have e := congrFun (congrFun hrel 0) 2
  simp [u02, Matrix.mul_apply, Fin.sum_univ_four] at e
  have e' : (b ^ 2 - a ^ 2) * (b ^ 2 + a ^ 2) = 0 := by linear_combination e
  have hAA : ((A * A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      !![a ^ 2, 0, 0, 0; 0, a ^ 2, 0, 0; 0, 0, b ^ 2, 0; 0, 0, 0, b ^ 2] := by
    simp only [Units.val_mul, hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  rcases mul_eq_zero.mp e' with h | h
  · left
    have hb2 : b ^ 2 = a ^ 2 := by linear_combination h
    rw [conjAut_eq_of_smul (A * A) 1 (a ^ 2) (pow_ne_zero 2 ha) ?_, map_one]
    rw [hAA, hb2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · right
    have hb2 : b ^ 2 = -a ^ 2 := by linear_combination h
    rw [conjAut_eq_of_smul (A * A) (Matrix.SpecialLinearGroup.toGL (rootInv F
      (show 2 ≤ 4 by norm_num))) (-a ^ 2) (neg_ne_zero.mpr (pow_ne_zero 2 ha)) ?_, conjAut_toGL]
    rw [hAA, coe_toGL_rootInv, hb2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem dual_sq_apply (A : GL (Fin 4) F)
    (hZ1 : (A : Matrix (Fin 4) (Fin 4) F) *
      (((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))ᵀ = -1)
    (hZ2 : (A : Matrix (Fin 4) (Fin 4) F)ᵀ *
      ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = -1) (s : SL(4, F)) :
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F A
      ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F A
        ((s⁻¹).transpose))⁻¹).transpose = s := by
  set u := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 4 F A
    ((s⁻¹).transpose) with hu
  have hMN : (A : Matrix (Fin 4) (Fin 4) F) *
      ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNM : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (A : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hSS : (s : Matrix (Fin 4) (Fin 4) F) *
      ((s⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hU : (u : Matrix (Fin 4) (Fin 4) F) = (A : Matrix (Fin 4) (Fin 4) F) *
      (((s⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F))ᵀ *
        ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    rw [hu, coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose]
  have hUi : ((u⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = (A : Matrix (Fin 4) (Fin 4) F) *
      (s : Matrix (Fin 4) (Fin 4) F)ᵀ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    have hQ : (u : Matrix (Fin 4) (Fin 4) F) * ((A : Matrix (Fin 4) (Fin 4) F) *
        (s : Matrix (Fin 4) (Fin 4) F)ᵀ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) =
        1 := by
      rw [hU]
      calc (A : Matrix (Fin 4) (Fin 4) F) *
            (((s⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F))ᵀ *
              ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
            ((A : Matrix (Fin 4) (Fin 4) F) * (s : Matrix (Fin 4) (Fin 4) F)ᵀ *
              ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
          = (A : Matrix (Fin 4) (Fin 4) F) *
              ((((s⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F))ᵀ *
                (((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
                  (A : Matrix (Fin 4) (Fin 4) F)) * (s : Matrix (Fin 4) (Fin 4) F)ᵀ) *
              ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by
            rw [hNM, Matrix.mul_one, ← Matrix.transpose_mul, hSS, Matrix.transpose_one,
              Matrix.mul_one, hMN]
    have hUUi : (u : Matrix (Fin 4) (Fin 4) F) * ((u⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
        1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hUiU : ((u⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (u : Matrix (Fin 4) (Fin 4) F) =
        1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc ((u⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)
        = ((u⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * ((u : Matrix (Fin 4) (Fin 4) F) *
            ((A : Matrix (Fin 4) (Fin 4) F) * (s : Matrix (Fin 4) (Fin 4) F)ᵀ *
              ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))) := by rw [hQ, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hUiU, Matrix.one_mul]
  apply Subtype.ext
  rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose, hUi, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  calc (A : Matrix (Fin 4) (Fin 4) F) *
        ((((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))ᵀ * ((s : Matrix (Fin 4) (Fin 4) F) *
          (A : Matrix (Fin 4) (Fin 4) F)ᵀ)) * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
      = ((A : Matrix (Fin 4) (Fin 4) F) *
          (((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))ᵀ) * (s : Matrix (Fin 4) (Fin 4) F) *
        ((A : Matrix (Fin 4) (Fin 4) F)ᵀ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
        simp only [Matrix.mul_assoc]
    _ = (s : Matrix (Fin 4) (Fin 4) F) := by rw [hZ1, hZ2]; simp

theorem sq_of_antidiag (A : GL (Fin 4) F) (m n : F) (hm : m ≠ 0) (hn : n ≠ 0)
    (hM : (A : Matrix (Fin 4) (Fin 4) F) =
      !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0]) :
    conjAut 4 F A * dualAut 4 F * (conjAut 4 F A * dualAut 4 F) = 1 := by
  have hN : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      !![0, -m⁻¹, 0, 0; m⁻¹, 0, 0, 0; 0, 0, 0, -n⁻¹; 0, 0, n⁻¹, 0] := by
    rw [Matrix.coe_units_inv, hM]
    refine Matrix.inv_eq_right_inv ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, hm, hn]
  have hZ1 : (A : Matrix (Fin 4) (Fin 4) F) *
      (((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))ᵀ = -1 := by
    rw [hN, hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, hm, hn]
  have hZ2 : (A : Matrix (Fin 4) (Fin 4) F)ᵀ *
      ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = -1 := by
    rw [hN, hM]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, hm, hn]
  ext p
  obtain ⟨s, rfl⟩ := proj_surjective 4 F p
  show conjAut 4 F A (dualAut 4 F (conjAut 4 F A (dualAut 4 F (proj 4 F s)))) = proj 4 F s
  rw [dualAut_proj, conjAut_proj, dualAut_proj, conjAut_proj, dual_sq_apply A hZ1 hZ2 s]

theorem aut_fix_blocks [Finite F] (h2 : (2 : F) ≠ 0) (α : MulAut (projectiveSL 4 F))
    (hfix : ∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range, α (proj 4 F r) = proj 4 F r)
    (hfix' : ∀ r ∈ (blockSL F 4 2 2 (by norm_num)).range, α (proj 4 F r) = proj 4 F r)
    (hα4 : α * α * (α * α) = 1) :
    α * α = 1 ∨ α * α = MulAut.conj (proj 4 F (rootInv F (show 2 ≤ 4 by norm_num))) := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hform α
  interval_cases ε
  · rw [pow_zero, mul_one] at hαeq
    subst hαeq
    obtain ⟨hσ, a, b, ha, hb, hM⟩ := aut_fix_blocks_zero h2 A σ hfix hfix'
    subst hσ
    have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
    rw [h1, mul_one] at hα4 ⊢
    exact sq_of_diag h2 A a b ha hM hα4
  · rw [pow_one] at hαeq
    subst hαeq
    obtain ⟨hσ, m, n, hm, hn, hM⟩ := aut_fix_blocks_one h2 A σ hfix hfix'
    subst hσ
    have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
    rw [h1, mul_one]
    left
    exact sq_of_antidiag A m n hm hn hM

theorem negBlock_four_two :
    negBlock F 4 2 = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
  rw [negBlock_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem twin_std (h2 : (2 : F) ≠ 0) {R R' : Subgroup SL(4, F)}
    (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num)) (hne : R ≠ R') {x x' : SL(4, F)}
    (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1)
    (hx'1 : x' ≠ 1) (hc : x' * x⁻¹ ∈ Subgroup.center SL(4, F)) :
    ∃ g : SL(4, F),
      R = (blockSL F 4 2 0 (by norm_num)).range.map (MulAut.conj g).toMonoidHom ∧
      R' = (blockSL F 4 2 2 (by norm_num)).range.map (MulAut.conj g).toMonoidHom ∧
      x = g * rootInv F (show 2 ≤ 4 by norm_num) * g⁻¹ := by
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hxi : x = i := hi.eq_of_orderOf_eq_two h2 hxR (orderOf_eq_prime (by rwa [pow_two]) hx1)
  have hxi' : x' = i' :=
    hi'.eq_of_orderOf_eq_two h2 hx'R' (orderOf_eq_prime (by rwa [pow_two]) hx'1)
  have hRlr := hi.eq_longRootGroup h2
  have hR'lr := hi'.eq_longRootGroup h2
  obtain ⟨g, hRg, hig⟩ := hi
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hxx : ((x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hx2, Matrix.SpecialLinearGroup.coe_one]
  have hxx' : ((x' : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (x' : Matrix (Fin 4) (Fin 4) F) =
      1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hx'2, Matrix.SpecialLinearGroup.coe_one]
  have hx'x : (x' : Matrix (Fin 4) (Fin 4) F) = r • (x : Matrix (Fin 4) (Fin 4) F) := by
    have h1 : (x' : Matrix (Fin 4) (Fin 4) F) =
        ((x' * x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
    rw [h1, ← hrA, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
      Matrix.one_mul]
  have hr2 : r * r = 1 := by
    have h1 : ((x' : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (x' : Matrix (Fin 4) (Fin 4) F) =
        (r * r) • (1 : Matrix (Fin 4) (Fin 4) F) := by
      rw [hx'x, Matrix.smul_mul, Matrix.mul_smul, hxx, smul_smul]
    rw [hxx'] at h1
    have := congrFun (congrFun h1 0) 0
    simpa using this.symm
  rcases mul_self_eq_one_iff.mp hr2 with hr1 | hr1
  · exfalso
    apply hne
    have hxx'' : x' = x := by
      apply Subtype.ext
      rw [hx'x, hr1, one_smul]
    rw [hRlr, hR'lr, ← hxi, ← hxi', hxx'']
  · refine ⟨g, hRg, ?_, hxi.trans hig⟩
    have hneg : -(!![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) F) =
        !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp
    have hX' : (x' : Matrix (Fin 4) (Fin 4) F) = (g : Matrix (Fin 4) (Fin 4) F) *
        negBlock F 4 2 * ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) := by
      rw [hx'x, hr1, neg_one_smul, hxi, hig, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, coe_rootInv, negBlock_four, negBlock_four_two,
        ← hneg, Matrix.mul_neg, Matrix.neg_mul]
    rw [hR'lr, ← hxi', hX', longRootGroup_conj, range_blockSL_eq_longRootGroup h2]

theorem psl4_autVac [Finite F] (h2 : (2 : F) ≠ 0) {R R' : Subgroup SL(4, F)}
    (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num)) (hne : R ≠ R') {x x' : SL(4, F)}
    (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1)
    (hx'1 : x' ≠ 1) (hc : x' * x⁻¹ ∈ Subgroup.center SL(4, F)) (φ : MulAut (projectiveSL 4 F))
    (hφ : ∀ r ∈ R, φ (proj 4 F r) = proj 4 F r) (hφ' : ∀ r ∈ R', φ (proj 4 F r) = proj 4 F r)
    (hφ4 : φ * φ * (φ * φ) = 1) :
    φ * φ = 1 ∨ φ * φ = MulAut.conj (proj 4 F x) := by
  obtain ⟨g, hRg, hR'g, hxg⟩ := twin_std h2 hR hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  set c : MulAut (projectiveSL 4 F) := MulAut.conj (proj 4 F g) with hcdef
  have hcp : ∀ s : SL(4, F), c (proj 4 F s) = proj 4 F (g * s * g⁻¹) := fun s => by
    rw [hcdef, MulAut.conj_apply, map_mul, map_mul, map_inv]
  set α : MulAut (projectiveSL 4 F) := c⁻¹ * φ * c with hα
  have hαp : ∀ s : SL(4, F), α (proj 4 F s) = (c⁻¹) (φ (c (proj 4 F s))) := fun s => rfl
  have hfixα : ∀ (S : Subgroup SL(4, F)), (∀ r ∈ S.map (MulAut.conj g).toMonoidHom,
      φ (proj 4 F r) = proj 4 F r) → ∀ r ∈ S, α (proj 4 F r) = proj 4 F r := by
    intro S hS r hr
    have hmem : g * r * g⁻¹ ∈ S.map (MulAut.conj g).toMonoidHom := ⟨r, hr, rfl⟩
    rw [hαp, hcp, hS _ hmem, ← hcp]
    simp
  have hα4 : α * α * (α * α) = 1 := by
    calc α * α * (α * α) = c⁻¹ * (φ * φ * (φ * φ)) * c := by rw [hα]; group
      _ = 1 := by rw [hφ4]; group
  have hfix0 := hfixα (blockSL F 4 2 0 (by norm_num)).range (hRg ▸ hφ)
  have hfix2 := hfixα (blockSL F 4 2 2 (by norm_num)).range (hR'g ▸ hφ')
  have hsq : φ * φ = c * (α * α) * c⁻¹ := by rw [hα]; group
  rcases aut_fix_blocks h2 α hfix0 hfix2 hα4 with h | h
  · left
    rw [hsq, h]
    group
  · right
    rw [hsq, h, hxg]
    have : MulAut.conj (proj 4 F (g * rootInv F (show 2 ≤ 4 by norm_num) * g⁻¹)) =
        c * MulAut.conj (proj 4 F (rootInv F (show 2 ≤ 4 by norm_num))) * c⁻¹ := by
      rw [hcdef]
      simp only [map_mul, map_inv]
    rw [this]

end CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
