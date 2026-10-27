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
public import Mathlib.RingTheory.WittVector.IsPoly
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

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem unit_separated_polynomial_projector {ring index : Type*}
    [CommRing ring] [Fintype index] (scalar : index → ring) (support : Finset index)
    (hunits : ∀ left ∈ support, ∀ right ∉ support, IsUnit (scalar left - scalar right)) :
    ∃ polynomial : Polynomial ring,
      ∀ label, polynomial.eval (scalar label) = if label ∈ support then 1 else 0 := by
  let inside : Polynomial ring := ∏ label ∈ support, (Polynomial.X - Polynomial.C (scalar label))
  let outside : Polynomial ring := ∏ label ∈ supportᶜ, (Polynomial.X - Polynomial.C (scalar label))
  have hcoprime : IsCoprime inside outside := by
    apply IsCoprime.prod_left
    intro left hleft
    apply IsCoprime.prod_right
    intro right hright
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (hunits left hleft right (Finset.mem_compl.mp hright))
  obtain ⟨first, second, hbezout⟩ := hcoprime
  refine ⟨second * outside, ?_⟩
  intro label
  by_cases hlabel : label ∈ support
  · have hroot : inside.eval (scalar label) = 0 := by
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero hlabel
      simp
    have hequal := congrArg (Polynomial.eval (scalar label)) hbezout
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, hroot, mul_zero,
      zero_add, Polynomial.eval_one, ite_eq_left hlabel] using hequal
  · have hroot : outside.eval (scalar label) = 0 := by
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_compl.mpr hlabel)
      simp
    simp only [Polynomial.eval_mul, hroot, mul_zero, ite_eq_right hlabel]

end CFSG.TwoRankLowerBound.Helpers
