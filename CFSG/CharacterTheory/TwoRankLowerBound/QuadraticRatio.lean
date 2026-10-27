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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.TwoRankLowerBound.Helpers

theorem three_term_quadratic_ratio {field : Type*} [Field field]
    (leftDegree rightDegree sumDegree leftValue rightValue sumValue : field)
    (hleft : leftDegree ≠ 0) (hright : rightDegree ≠ 0) (hsum : sumDegree ≠ 0)
    (hdegrees : sumDegree = -leftDegree - rightDegree)
    (hvalues : sumValue = leftValue + rightValue)
    (hquadratic : leftValue ^ 2 / leftDegree + rightValue ^ 2 / rightDegree +
      sumValue ^ 2 / sumDegree = 0) :
    leftValue / leftDegree = rightValue / rightDegree := by
  have hcombined : (leftValue * rightDegree - rightValue * leftDegree) ^ 2 = 0 := by
    rw [hdegrees, hvalues] at hquadratic
    have hdenominator : -leftDegree - rightDegree ≠ 0 := by rw [← hdegrees]; exact hsum
    field_simp [hleft, hright, hdenominator] at hquadratic
    linear_combination -hquadratic
  have hcross : leftValue * rightDegree = rightValue * leftDegree := by
    apply sub_eq_zero.mp
    exact (pow_eq_zero_iff (by omega : (2 : ℕ) ≠ 0)).mp hcombined
  exact (div_eq_div_iff hleft hright).mpr hcross

end CFSG.TwoRankLowerBound.Helpers
