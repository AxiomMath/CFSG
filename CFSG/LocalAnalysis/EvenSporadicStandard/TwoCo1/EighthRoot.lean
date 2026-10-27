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

namespace CFSG.EvenSporadicStandard.TwoCo1

open Subgroup

theorem no_eighth_root_of_lift {L X : Type*} [Group L] [Group X] (π : L →* X) {z : L}
    (hker : π.ker = zpowers z) (hz1 : z ≠ 1) (B : X → Prop)
    (hlift : ∀ w : L, π w ^ 2 = 1 → ¬ B (π w) → w ^ 2 = 1)
    (hfour : ∀ y : X, ¬ B (y ^ 4)) : ∀ y : L, y ^ 8 ≠ z := by
  intro y hy
  have hw2 : (y ^ 4) ^ 2 = z := by rw [← pow_mul]; exact hy
  have hπz : π z = 1 := MonoidHom.mem_ker.1 (hker ▸ mem_zpowers z)
  have hπw : π (y ^ 4) ^ 2 = 1 := by rw [← map_pow, hw2, hπz]
  have hB : ¬ B (π (y ^ 4)) := by
    rw [map_pow]
    exact hfour (π y)
  exact hz1 (hw2.symm.trans (hlift _ hπw hB))

end CFSG.EvenSporadicStandard.TwoCo1
