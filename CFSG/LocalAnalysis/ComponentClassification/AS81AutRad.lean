module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenAut

public noncomputable section

namespace CFSG.ComponentClassification.AS81

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.ComponentClassification.RankTwoL3Even

variable {F : Type} [Field F]

theorem mul_unipU_one_apply (M : Matrix (Fin 3) (Fin 3) F) (s : F) (i j : Fin 3) :
    (M * (unipU F s 0 0 : Matrix (Fin 3) (Fin 3) F)) i j =
      M i j + if j = 1 then s * M i 0 else 0 := by
  rw [coe_unipU]
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three]; try ring)

theorem unipU_one_mul_apply (M : Matrix (Fin 3) (Fin 3) F) (s : F) (i j : Fin 3) :
    ((unipU F s 0 0 : Matrix (Fin 3) (Fin 3) F) * M) i j =
      M i j + if i = 0 then s * M 1 j else 0 := by
  rw [coe_unipU]
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three]; try ring)

theorem mul_unipU_two_apply (M : Matrix (Fin 3) (Fin 3) F) (s : F) (i j : Fin 3) :
    (M * (unipU F 0 s 0 : Matrix (Fin 3) (Fin 3) F)) i j =
      M i j + if j = 2 then s * M i 1 else 0 := by
  rw [coe_unipU]
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three]; try ring)

theorem unipU_two_mul_apply (M : Matrix (Fin 3) (Fin 3) F) (s : F) (i j : Fin 3) :
    ((unipU F 0 s 0 : Matrix (Fin 3) (Fin 3) F) * M) i j =
      M i j + if i = 1 then s * M 2 j else 0 := by
  rw [coe_unipU]
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three]; try ring)

theorem mul_unipU_one_transpose_apply (M : Matrix (Fin 3) (Fin 3) F) (s : F) (i j : Fin 3) :
    (M * ((unipU F s 0 0).transpose : Matrix (Fin 3) (Fin 3) F)) i j =
      M i j + if j = 0 then s * M i 1 else 0 := by
  rw [SpecialLinearGroup.coe_transpose, coe_unipU]
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]; try ring)

theorem mul_unipU_two_transpose_apply (M : Matrix (Fin 3) (Fin 3) F) (s : F) (i j : Fin 3) :
    (M * ((unipU F 0 s 0).transpose : Matrix (Fin 3) (Fin 3) F)) i j =
      M i j + if j = 1 then s * M i 2 else 0 := by
  rw [SpecialLinearGroup.coe_transpose, coe_unipU]
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]; try ring)

theorem trace_unipU_transpose (a b c : F) :
    trace ((unipU F a b c).transpose : Matrix (Fin 3) (Fin 3) F) =
      trace (unipU F a b c : Matrix (Fin 3) (Fin 3) F) := by
  rw [SpecialLinearGroup.coe_transpose, trace_transpose]

variable [CharP F 2]

theorem dualAut_proj_unipU_of_mul_eq_zero {a b : F} (hab : a * b = 0) :
    dualAut 3 F (proj 3 F (unipU F a b 0)) = proj 3 F (unipU F a b 0).transpose := by
  rw [dualAut_proj, unipU_inv]
  simp only [CharTwo.neg_eq, hab, zero_add]

theorem trace_unipU_ne_zero (a b c : F) : trace (unipU F a b c : Matrix (Fin 3) (Fin 3) F) ≠ 0 := by
  rw [trace_unipU, three_eq_one_of_charTwo]
  exact one_ne_zero

variable [Finite F]

theorem exists_eq_conj_of_fix_projRad_zero {α : MulAut (projectiveSL 3 F)}
    (hα : ∀ x ∈ projRad F 0, α x = x) : ∃ r ∈ projRad F 0, α = MulAut.conj r := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := F) (n := 3) le_rfl).2 α
  have hz : ∀ c : F, (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F ^ ε)
      (proj 3 F (unipU F 0 0 c)) = proj 3 F (unipU F 0 0 c) := fun c =>
    hα _ (mem_projRad_zero.2 ⟨0, c, rfl⟩)
  have hfix := hα _ (mem_projRad_zero.2 ⟨1, 0, rfl⟩)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  ·
    simp only [pow_zero, mul_one] at hz hfix ⊢
    obtain ⟨hσ, h10, h20, h21, h22⟩ := fix_center_of_semilinear (A := A) (σ := σ) hz
    subst hσ
    set M := (A : Matrix (Fin 3) (Fin 3) F) with hM
    have hdet : M.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
    simp only [map_one, mul_one] at hfix ⊢
    have key := mul_eq_mul_of_conjAut_proj_eq rfl (trace_unipU_ne_zero 1 0 0) hfix
    have e : ∀ i j : Fin 3, M i j + (if j = 1 then 1 * M i 0 else 0) =
        M i j + if i = 0 then 1 * M 1 j else 0 := by
      intro i j
      have := congrFun (congrFun key i) j
      rwa [mul_unipU_one_apply, unipU_one_mul_apply] at this
    have e01 := e 0 1
    have e02 := e 0 2
    simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, one_mul, add_zero] at e01 e02
    have h11 : M 1 1 = M 0 0 := by linear_combination -e01
    have h12 : M 1 2 = 0 := by linear_combination -e02
    rw [Matrix.det_fin_three, h10, h20, h21, h22, h11, h12] at hdet
    have h00 : M 0 0 ≠ 0 := fun h => hdet (by rw [h]; ring)
    set u := unipU F (M 0 1 / M 0 0) 0 (M 0 2 / M 0 0) with hu
    have hA : A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (M 0 0) h00) *
        Matrix.SpecialLinearGroup.toGL u := by
      apply Units.ext
      rw [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hu, coe_unipU]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [GeneralLinearGroup.scalar, ← hM, h10, h20, h21, h22, h11, h12] <;> field_simp
    refine ⟨proj 3 F u, mem_projRad_zero.2 ⟨_, _, rfl⟩, ?_⟩
    rw [hA, map_mul, conjAut_scalar, one_mul, conjAut_toGL]
  ·
    exfalso
    simp only [pow_one] at hz hfix
    obtain ⟨hσ, h12, h21, h22, h20⟩ := fix_center_of_graph (A := A) (σ := σ) hz
    subst hσ
    set M := (A : Matrix (Fin 3) (Fin 3) F) with hM
    have hdet : M.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
    simp only [map_one, MulAut.one_apply, MulAut.mul_apply] at hfix
    rw [dualAut_proj_unipU_of_mul_eq_zero (mul_zero 1)] at hfix
    have key := mul_eq_mul_of_conjAut_proj_eq (trace_unipU_transpose 1 0 0)
      (trace_unipU_ne_zero 1 0 0) hfix
    have e : ∀ i j : Fin 3, M i j + (if j = 0 then 1 * M i 1 else 0) =
        M i j + if i = 0 then 1 * M 1 j else 0 := by
      intro i j
      have := congrFun (congrFun key i) j
      rwa [mul_unipU_one_transpose_apply, unipU_one_mul_apply] at this
    have e10 := e 1 0
    simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, one_mul, add_zero] at e10
    have h11 : M 1 1 = 0 := by linear_combination e10
    apply hdet
    rw [Matrix.det_fin_three, h11, h12, h21, h22]
    ring

theorem exists_eq_conj_of_fix_projRad_one {α : MulAut (projectiveSL 3 F)}
    (hα : ∀ x ∈ projRad F 1, α x = x) : ∃ r ∈ projRad F 1, α = MulAut.conj r := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := F) (n := 3) le_rfl).2 α
  have hz : ∀ c : F, (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F ^ ε)
      (proj 3 F (unipU F 0 0 c)) = proj 3 F (unipU F 0 0 c) := fun c =>
    hα _ (mem_projRad_one.2 ⟨0, c, rfl⟩)
  have hfix := hα _ (mem_projRad_one.2 ⟨1, 0, rfl⟩)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  ·
    simp only [pow_zero, mul_one] at hz hfix ⊢
    obtain ⟨hσ, h10, h20, h21, h22⟩ := fix_center_of_semilinear (A := A) (σ := σ) hz
    subst hσ
    set M := (A : Matrix (Fin 3) (Fin 3) F) with hM
    have hdet : M.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
    simp only [map_one, mul_one] at hfix ⊢
    have key := mul_eq_mul_of_conjAut_proj_eq rfl (trace_unipU_ne_zero 0 1 0) hfix
    have e : ∀ i j : Fin 3, M i j + (if j = 2 then 1 * M i 1 else 0) =
        M i j + if i = 1 then 1 * M 2 j else 0 := by
      intro i j
      have := congrFun (congrFun key i) j
      rwa [mul_unipU_two_apply, unipU_two_mul_apply] at this
    have e12 := e 1 2
    have e02 := e 0 2
    simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, one_mul, add_zero] at e12 e02
    have h11 : M 1 1 = M 0 0 := by linear_combination e12 + h22
    have h01 : M 0 1 = 0 := by linear_combination e02
    rw [Matrix.det_fin_three, h10, h20, h21, h22, h11, h01] at hdet
    have h00 : M 0 0 ≠ 0 := fun h => hdet (by rw [h]; ring)
    set u := unipU F 0 (M 1 2 / M 0 0) (M 0 2 / M 0 0) with hu
    have hA : A = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (M 0 0) h00) *
        Matrix.SpecialLinearGroup.toGL u := by
      apply Units.ext
      rw [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hu, coe_unipU]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [GeneralLinearGroup.scalar, ← hM, h10, h20, h21, h22, h11, h01] <;> field_simp
    refine ⟨proj 3 F u, mem_projRad_one.2 ⟨_, _, rfl⟩, ?_⟩
    rw [hA, map_mul, conjAut_scalar, one_mul, conjAut_toGL]
  ·
    exfalso
    simp only [pow_one] at hz hfix
    obtain ⟨hσ, h12, h21, h22, h20⟩ := fix_center_of_graph (A := A) (σ := σ) hz
    subst hσ
    set M := (A : Matrix (Fin 3) (Fin 3) F) with hM
    have hdet : M.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
    simp only [map_one, MulAut.one_apply, MulAut.mul_apply] at hfix
    rw [dualAut_proj_unipU_of_mul_eq_zero (zero_mul 1)] at hfix
    have key := mul_eq_mul_of_conjAut_proj_eq (trace_unipU_transpose 0 1 0)
      (trace_unipU_ne_zero 0 1 0) hfix
    have e : ∀ i j : Fin 3, M i j + (if j = 1 then 1 * M i 2 else 0) =
        M i j + if i = 1 then 1 * M 2 j else 0 := by
      intro i j
      have := congrFun (congrFun key i) j
      rwa [mul_unipU_two_transpose_apply, unipU_two_mul_apply] at this
    have e01 := e 0 1
    simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, one_mul, add_zero] at e01
    have h02 : M 0 2 = 0 := by linear_combination e01
    apply hdet
    rw [Matrix.det_fin_three, h20, h02, h21, h22]
    ring

theorem exists_eq_conj_of_fix_projRad (i : Fin 2) {α : MulAut (projectiveSL 3 F)}
    (hα : ∀ x ∈ projRad F i, α x = x) : ∃ r ∈ projRad F i, α = MulAut.conj r := by
  fin_cases i
  · exact exists_eq_conj_of_fix_projRad_zero hα
  · exact exists_eq_conj_of_fix_projRad_one hα

end CFSG.ComponentClassification.AS81
