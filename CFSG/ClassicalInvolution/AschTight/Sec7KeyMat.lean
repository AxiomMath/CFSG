module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7

open Matrix

variable {F : Type*} [Field F]

theorem mul_eq_mul_of_minors {xi xj xk yi yj yk wi wj wk : F} (hk : wk ≠ 0)
    (hxi : xi * wk = xk * wi) (hxj : xj * wk = xk * wj) (hyi : yi * wk = yk * wi)
    (hyj : yj * wk = yk * wj) : xi * yj = xj * yi := by
  refine mul_left_cancel₀ (pow_ne_zero 2 hk) ?_
  linear_combination (yj * wk) * hxi + (xk * wi) * hyj - (yi * wk) * hxj - (xk * wj) * hyi

theorem matrix_commute_of_commute_nonscalar {A B C : Matrix (Fin 2) (Fin 2) F}
    (hA : ¬ (A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 0 0 = A 1 1)) (hB : B * A = A * B)
    (hC : C * A = A * C) : B * C = C * B := by
  have hB00 := congrFun (congrFun hB 0) 0
  have hB01 := congrFun (congrFun hB 0) 1
  have hB10 := congrFun (congrFun hB 1) 0
  have hC00 := congrFun (congrFun hC 0) 0
  have hC01 := congrFun (congrFun hC 0) 1
  have hC10 := congrFun (congrFun hC 1) 0
  simp only [mul_apply, Fin.sum_univ_two] at hB00 hB01 hB10 hC00 hC01 hC10
  have hx12 : B 0 1 * A 1 0 = B 1 0 * A 0 1 := by linear_combination hB00
  have hx13 : B 0 1 * (A 0 0 - A 1 1) = (B 0 0 - B 1 1) * A 0 1 := by linear_combination -hB01
  have hx23 : B 1 0 * (A 0 0 - A 1 1) = (B 0 0 - B 1 1) * A 1 0 := by linear_combination hB10
  have hy12 : C 0 1 * A 1 0 = C 1 0 * A 0 1 := by linear_combination hC00
  have hy13 : C 0 1 * (A 0 0 - A 1 1) = (C 0 0 - C 1 1) * A 0 1 := by linear_combination -hC01
  have hy23 : C 1 0 * (A 0 0 - A 1 1) = (C 0 0 - C 1 1) * A 1 0 := by linear_combination hC10
  have key : B 0 1 * C 1 0 = B 1 0 * C 0 1 ∧ B 0 1 * (C 0 0 - C 1 1) = (B 0 0 - B 1 1) * C 0 1 ∧
      B 1 0 * (C 0 0 - C 1 1) = (B 0 0 - B 1 1) * C 1 0 := by
    have hw : A 0 1 ≠ 0 ∨ A 1 0 ≠ 0 ∨ A 0 0 - A 1 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact hA ⟨h.1, h.2.1, sub_eq_zero.mp h.2.2⟩
    rcases hw with h | h | h
    · exact ⟨mul_eq_mul_of_minors h rfl hx12.symm rfl hy12.symm,
        mul_eq_mul_of_minors h rfl hx13.symm rfl hy13.symm,
        mul_eq_mul_of_minors h hx12.symm hx13.symm hy12.symm hy13.symm⟩
    · exact ⟨mul_eq_mul_of_minors h hx12 rfl hy12 rfl,
        mul_eq_mul_of_minors h hx12 hx23.symm hy12 hy23.symm,
        mul_eq_mul_of_minors h rfl hx23.symm rfl hy23.symm⟩
    · exact ⟨mul_eq_mul_of_minors h hx13 hx23 hy13 hy23,
        mul_eq_mul_of_minors h hx13 rfl hy13 rfl,
        mul_eq_mul_of_minors h hx23 rfl hy23 rfl⟩
  obtain ⟨k1, k2, k3⟩ := key
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [mul_apply, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination k1
  · linear_combination -k2
  · linear_combination k3
  · linear_combination -k1

theorem sl2_commute_of_commute {x y y' : SpecialLinearGroup (Fin 2) F} (hx : x * x ≠ 1)
    (hy : y * x = x * y) (hy' : y' * x = x * y') : y * y' = y' * y := by
  have hA : ¬ ((x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (x : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      (x : Matrix (Fin 2) (Fin 2) F) 0 0 = (x : Matrix (Fin 2) (Fin 2) F) 1 1) := by
    rintro ⟨h01, h10, h00⟩
    apply hx
    have hdet := x.2
    rw [det_fin_two, h01, h10, ← h00] at hdet
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_two, h01, h10, ← h00] <;>
      linear_combination hdet
  have hy₀ : (y : Matrix (Fin 2) (Fin 2) F) * x = x * y := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hy
    simpa using this
  have hy₀' : (y' : Matrix (Fin 2) (Fin 2) F) * x = x * y' := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hy'
    simpa using this
  exact Subtype.ext (matrix_commute_of_commute_nonscalar hA hy₀ hy₀')

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec7
