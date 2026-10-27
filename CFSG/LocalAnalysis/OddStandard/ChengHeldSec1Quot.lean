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

namespace CFSG.OddStandard.ChengHeld.Sec1

open Subgroup

theorem exists_conj_of_orderOf_two {A' : Type*} [Group A']
    (hinv : ∀ x y : A' ⧸ center A', orderOf x = 2 → orderOf y = 2 → IsConj x y)
    {x y : A'} (hx : x * x = 1) (hy : y * y = 1) (hx1 : x ∉ center A') (hy1 : y ∉ center A') :
    ∃ a : A', ∃ z ∈ center A', a⁻¹ * x * a = z * y := by
  have hord : ∀ w : A', w * w = 1 → w ∉ center A' →
      orderOf (QuotientGroup.mk w : A' ⧸ center A') = 2 := by
    intro w hw hw1
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← QuotientGroup.mk_mul, hw, QuotientGroup.mk_one]
    · intro h
      exact hw1 ((QuotientGroup.eq_one_iff w).mp h)
  obtain ⟨c, hc⟩ := isConj_iff.mp (hinv _ _ (hord x hx hx1) (hord y hy hy1))
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective c
  have h2 : (QuotientGroup.mk y : A' ⧸ center A') = QuotientGroup.mk (a' * x * a'⁻¹) := by
    rw [← hc]
    rfl
  have h3 := QuotientGroup.eq.mp h2
  refine ⟨a'⁻¹, y⁻¹ * (a' * x * a'⁻¹), h3, ?_⟩
  rw [inv_inv, ← Subgroup.mem_center_iff.mp h3 y, mul_inv_cancel_left]

end CFSG.OddStandard.ChengHeld.Sec1
