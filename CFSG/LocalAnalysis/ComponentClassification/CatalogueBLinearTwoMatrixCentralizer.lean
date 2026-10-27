module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.ComponentClassification.CatalogueBLinearTwo

open Matrix

theorem commuting_matrix_scalar_expression {K : Type*} [Field K]
    (A B : Matrix (Fin 2) (Fin 2) K) (hab : A 0 1 ≠ 0)
    (hcommute : A * B = B * A) :
    B = (B 0 0 - (B 0 1 / A 0 1) * A 0 0) • (1 : Matrix (Fin 2) (Fin 2) K) +
      (B 0 1 / A 0 1) • A := by
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hcommute
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hcommute
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  ext i j
  fin_cases i <;> fin_cases j <;> simp [smul_eq_mul] <;> field_simp [hab] <;>
    first | (solve | ring) | (solve | linear_combination h00) |
      (solve | linear_combination h01)

theorem commuting_matrices_of_upper_right_ne_zero {K : Type*} [Field K]
    (A B C : Matrix (Fin 2) (Fin 2) K) (hab : A 0 1 ≠ 0)
    (hB : A * B = B * A) (hC : A * C = C * A) : B * C = C * B := by
  rw [commuting_matrix_scalar_expression A B hab hB]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hC]

theorem nonscalar_matrix_centralizer_commutative {K : Type*} [Field K]
    (A B C : Matrix (Fin 2) (Fin 2) K)
    (hnonscalar : ¬ ∃ a : K, A = Matrix.scalar (Fin 2) a)
    (hB : A * B = B * A) (hC : A * C = C * A) : B * C = C * B := by
  by_cases hab : A 0 1 = 0
  · by_cases hac : A 1 0 = 0
    · have had : A 0 0 ≠ A 1 1 := by
        intro had
        apply hnonscalar
        refine ⟨A 0 0, ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.scalar, hab, hac, had]
      have hB01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hB
      have hB10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hB
      have hC01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hC
      have hC10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 1 0) hC
      simp only [Matrix.mul_apply, Fin.sum_univ_two, hab, hac, mul_zero, zero_mul,
        zero_add, add_zero] at hB01 hB10 hC01 hC10
      have hb : B 0 1 = 0 := by
        apply (mul_eq_zero.mp (show (A 0 0 - A 1 1) * B 0 1 = 0 by
          linear_combination hB01)).resolve_left (sub_ne_zero.mpr had)
      have hc : B 1 0 = 0 := by
        apply (mul_eq_zero.mp (show (A 0 0 - A 1 1) * B 1 0 = 0 by
          linear_combination -hB10)).resolve_left (sub_ne_zero.mpr had)
      have hd : C 0 1 = 0 := by
        apply (mul_eq_zero.mp (show (A 0 0 - A 1 1) * C 0 1 = 0 by
          linear_combination hC01)).resolve_left (sub_ne_zero.mpr had)
      have he : C 1 0 = 0 := by
        apply (mul_eq_zero.mp (show (A 0 0 - A 1 1) * C 1 0 = 0 by
          linear_combination -hC10)).resolve_left (sub_ne_zero.mpr had)
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, hb, hc, hd, he, mul_comm]
    · have hBT : A.transpose * B.transpose = B.transpose * A.transpose := by
        simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose hB.symm
      have hCT : A.transpose * C.transpose = C.transpose * A.transpose := by
        simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose hC.symm
      have h := commuting_matrices_of_upper_right_ne_zero A.transpose B.transpose
        C.transpose hac hBT hCT
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
        congrArg Matrix.transpose h.symm
  · exact commuting_matrices_of_upper_right_ne_zero A B C hab hB hC

end CFSG.ComponentClassification.CatalogueBLinearTwo
