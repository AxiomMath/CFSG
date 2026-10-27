module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix

lemma sec12S8Mod_tora_conj_mul {K : Type} [Field K]
    {P A B : Matrix (Fin 2) (Fin 2) K} (hP : IsUnit P.det) :
    (P * A * P⁻¹) * (P * B * P⁻¹) = P * (A * B) * P⁻¹ := by
  calc (P * A * P⁻¹) * (P * B * P⁻¹)
      = P * A * (P⁻¹ * P) * B * P⁻¹ := by noncomm_ring
    _ = P * A * 1 * B * P⁻¹ := by rw [Matrix.nonsing_inv_mul P hP]
    _ = P * (A * B) * P⁻¹ := by noncomm_ring

lemma sec12S8Mod_tora_conj_inv {K : Type} [Field K]
    {P A : Matrix (Fin 2) (Fin 2) K} (hP : IsUnit P.det) (hA : IsUnit A.det) :
    (P * A * P⁻¹)⁻¹ = P * A⁻¹ * P⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  calc (P * A * P⁻¹) * (P * A⁻¹ * P⁻¹)
      = P * A * (P⁻¹ * P) * A⁻¹ * P⁻¹ := by noncomm_ring
    _ = P * A * 1 * A⁻¹ * P⁻¹ := by rw [Matrix.nonsing_inv_mul P hP]
    _ = P * (A * A⁻¹) * P⁻¹ := by noncomm_ring
    _ = P * 1 * P⁻¹ := by rw [Matrix.mul_nonsing_inv A hA]
    _ = 1 := by rw [Matrix.mul_one, Matrix.mul_nonsing_inv P hP]

lemma sec12S8Mod_tora_conj_pow {K : Type} [Field K]
    {P A : Matrix (Fin 2) (Fin 2) K} (hP : IsUnit P.det) (n : ℕ) :
    (P * A * P⁻¹) ^ n = P * A ^ n * P⁻¹ := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Matrix.mul_one, Matrix.mul_nonsing_inv P hP]
  | succ n ih => rw [pow_succ, ih, pow_succ, sec12S8Mod_tora_conj_mul hP]

lemma sec12S8Mod_tora_coe_inv {K : Type} [Field K]
    (x : SpecialLinearGroup (Fin 2) K) :
    ((x⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (x : Matrix (Fin 2) (Fin 2) K)⁻¹ := by
  rw [SpecialLinearGroup.coe_inv]
  symm
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_adjugate, SpecialLinearGroup.det_coe, one_smul]

lemma sec12S8Mod_tora_diag_inv {K : Type} [Field K] {a : K} (ha : a ≠ 0) :
    (Matrix.diagonal ![a, a⁻¹])⁻¹ = Matrix.diagonal ![a⁻¹, a] := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [mul_inv_cancel₀ ha, inv_mul_cancel₀ ha]

lemma sec12S8Mod_tora_diag_comm {K : Type} [Field K] (a b : Fin 2 → K) :
    Matrix.diagonal a * Matrix.diagonal b = Matrix.diagonal b * Matrix.diagonal a := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

end CFSG.OddStandard.SmallF3.Omega
