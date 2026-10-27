module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonal

open Matrix

variable {K : Type*} [Field K]

@[expose] def planeGram (a b : K) : Matrix (Fin 2) (Fin 2) K := !![a, 0; 0, b]

theorem plane_matrix_shape (a b : K) (ha : a ≠ 0)
    (A : Matrix (Fin 2) (Fin 2) K) (hdet : A.det = 1)
    (hA : Aᵀ * planeGram a b * A = planeGram a b) :
    A = !![A 0 0, -(b / a) * A 1 0; A 1 0, A 0 0] := by
  have hright : A * A.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
  have hlinear : Aᵀ * planeGram a b = planeGram a b * A.adjugate := by
    calc
      Aᵀ * planeGram a b = Aᵀ * planeGram a b * (A * A.adjugate) := by
        rw [hright, Matrix.mul_one]
      _ = (Aᵀ * planeGram a b * A) * A.adjugate := by
        simp only [Matrix.mul_assoc]
      _ = planeGram a b * A.adjugate := by rw [hA]
  have h00 := congrFun₂ hlinear 0 0
  have h01 := congrFun₂ hlinear 0 1
  simp only [planeGram, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_zero, zero_mul, add_zero, zero_add] at h00 h01
  have hdiag : A 1 1 = A 0 0 := by
    exact (mul_left_cancel₀ ha (by simpa only [mul_comm] using h00)).symm
  have hoff : A 0 1 = -(b / a) * A 1 0 := by
    have heq : A 0 1 = -(b * A 1 0) / a := by
      apply (eq_div_iff ha).mpr
      linear_combination h01
    simpa only [neg_div, mul_div_right_comm, neg_mul] using heq
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hdiag, hoff]

theorem plane_matrices_commute (a b : K) (ha : a ≠ 0)
    (A C : Matrix (Fin 2) (Fin 2) K) (hAdet : A.det = 1) (hCdet : C.det = 1)
    (hA : Aᵀ * planeGram a b * A = planeGram a b)
    (hC : Cᵀ * planeGram a b * C = planeGram a b) : A * C = C * A := by
  conv_lhs => rw [plane_matrix_shape a b ha A hAdet hA,
    plane_matrix_shape a b ha C hCdet hC]
  conv_rhs => rw [plane_matrix_shape a b ha C hCdet hC,
    plane_matrix_shape a b ha A hAdet hA]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end CFSG.ComponentClassification.CatalogueBOrthogonal
