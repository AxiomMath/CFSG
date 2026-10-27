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

namespace CFSG.LocalAnalysis.GLTheoremA

theorem bijective_of_cover {G K X : Type} [Group G] [Finite G] [Group K] [Finite K] [Group X]
    (π : G →* X) (hπ : Function.Surjective π) (ρ : K →* X) (hρ : Function.Surjective ρ)
    (φ : G →* K) (hφ : Function.Surjective φ) (hcomp : ∀ g, ρ (φ g) = π g)
    (hker : Nat.card π.ker = Nat.card ρ.ker) : Function.Bijective φ := by
  have h1 : Nat.card π.ker * Nat.card X = Nat.card G := by
    have := Subgroup.card_ker_mul_card_range π
    rwa [MonoidHom.range_eq_top.2 hπ, Subgroup.card_top] at this
  have h2 : Nat.card ρ.ker * Nat.card X = Nat.card K := by
    have := Subgroup.card_ker_mul_card_range ρ
    rwa [MonoidHom.range_eq_top.2 hρ, Subgroup.card_top] at this
  refine hφ.bijective_of_nat_card_le ?_
  rw [← h1, ← h2, hker]

end CFSG.LocalAnalysis.GLTheoremA
