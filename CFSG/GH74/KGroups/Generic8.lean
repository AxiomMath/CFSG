module

import CFSG.GH74.E2.FrattiniRank
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

namespace CFSG.GH74.KGroups

theorem rank_ge_of_quotient {U : Type*} [Group U] [Finite U] (N : Subgroup U) [N.Normal]
    (hsq : ∀ x : U, x ^ 2 ∈ N) (hcomm : ∀ x y : U, x * y * (y * x)⁻¹ ∈ N) (r : ℕ)
    (hcard : Nat.card U = 2 ^ r * Nat.card N) : r ≤ Group.rank U := by
  have hcommY : ∀ a b : U ⧸ N, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
        simpa [div_eq_mul_inv] using hcomm x y
  have : IsMulCommutative (U ⧸ N) := ⟨⟨hcommY⟩⟩
  have hY2 : ∀ y : U ⧸ N, y ^ 2 = 1 := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hsq x
  have h1 := CFSG.GH74.E2.two_pow_rank_eq_card_of_exponent_two (Y := U ⧸ N) hY2
  have hq : Nat.card (U ⧸ N) * Nat.card N = Nat.card U :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have h2 : Nat.card (U ⧸ N) = 2 ^ r := by
    apply Nat.eq_of_mul_eq_mul_right hNpos
    rw [hq, hcard]
  have h3 : Group.rank (U ⧸ N) = r := by
    rw [h2] at h1
    exact (Nat.pow_right_injective le_rfl h1)
  rw [← h3]
  exact Group.rank_le_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end CFSG.GH74.KGroups
