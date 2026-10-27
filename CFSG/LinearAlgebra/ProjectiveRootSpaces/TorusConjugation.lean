module

public import CFSG.LinearAlgebra.ProjectiveRootSpaces.RootData

public section

namespace CFSG.LinearAlgebra.ProjectiveRootSpaces.TorusConjugation

open scoped MatrixGroups
open CFSG.LinearAlgebra.ProjectiveRootSpaces.UnipotentSubgroup
open CFSG.LinearAlgebra.ProjectiveRootSpaces.RootData

variable {F : Type} [Field F]

theorem diagonalSL_conj_upper (a : Fˣ) (x : F) :
    diagonalSL F a * upper F (Multiplicative.ofAdd x) * (diagonalSL F a)⁻¹ =
      upper F (Multiplicative.ofAdd (((a : F) ^ 2) * x)) := by
  apply Subtype.ext
  have hinv : ((diagonalSL F a)⁻¹ : SL(2, F)) =
      diagonalSL F a⁻¹ := by
    rw [← map_inv]
  rw [hinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, Fin.zero_eta, Fin.mk_one, Matrix.mul_apply, Fin.sum_univ_two, diagonalSL_apply_zero_zero,
      diagonalSL_apply_one_one, diagonalSL_apply_zero_one, diagonalSL_apply_one_zero,
      upper_apply_zero_zero, upper_apply_one_zero, upper_apply_one_one,
      upper_apply_zero_one, Units.val_inv_eq_inv_val, toAdd_ofAdd] <;> field_simp <;> ring

theorem diagonalPSL_conj_upperPSL (a : Fˣ) (x : F) :
    diagonalPSL F a * upperPSL F (Multiplicative.ofAdd x) * (diagonalPSL F a)⁻¹ =
      upperPSL F (Multiplicative.ofAdd (((a : F) ^ 2) * x)) := by
  rw [upperPSL_apply, upperPSL_apply, diagonalPSL_apply, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, diagonalSL_conj_upper]

theorem torus_le_normalizer_upperSubgroup : torus F ≤ Subgroup.normalizer (upperSubgroup F : Set PSL(2, F)) := by
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨Multiplicative.ofAdd (((a : F) ^ 2) * Multiplicative.toAdd b), ?_⟩
    rw [← diagonalPSL_conj_upperPSL]; rfl
  · rintro ⟨b, hb⟩
    refine ⟨Multiplicative.ofAdd (((a⁻¹ : Fˣ) : F) ^ 2 * Multiplicative.toAdd b), ?_⟩
    have := diagonalPSL_conj_upperPSL a⁻¹ (Multiplicative.toAdd b)
    rw [map_inv, ofAdd_toAdd, hb] at this
    simp only [inv_inv] at this
    rw [← this]
    group

end CFSG.LinearAlgebra.ProjectiveRootSpaces.TorusConjugation
