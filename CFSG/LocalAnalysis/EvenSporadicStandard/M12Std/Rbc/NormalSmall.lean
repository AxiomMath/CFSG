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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Subgroup

variable {P : Type*} [Group P]

private lemma card_le_two_mul_of_forall [Finite P] {J N : Subgroup P} {w : P}
    (h : ∀ g ∈ N, g ∈ J ∨ w⁻¹ * g ∈ J) :
    Nat.card ↥N ≤ 2 * Nat.card ↥J := by
  have hsub : (N : Set P) ⊆ (J : Set P) ∪ (fun y => w * y) '' (J : Set P) := by
    intro g hg
    rcases h g hg with hgJ | hgJ
    · exact Or.inl hgJ
    · exact Or.inr ⟨w⁻¹ * g, hgJ, mul_inv_cancel_left w g⟩
  calc
    Nat.card ↥N = (N : Set P).ncard := Nat.card_coe_set_eq _
    _ ≤ ((J : Set P) ∪ (fun y => w * y) '' (J : Set P)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (J : Set P).ncard + ((fun y => w * y) '' (J : Set P)).ncard :=
        Set.ncard_union_le _ _
    _ = 2 * Nat.card ↥J := by
        rw [Set.ncard_image_of_injective _ (mul_right_injective w)]
        have hJ : Nat.card ↥J = (J : Set P).ncard := Nat.card_coe_set_eq _
        rw [hJ]
        ring

private lemma covered_by_two [Finite P] {J N : Subgroup P} {w₁ w₂ x : P}
    (hJN : J ≤ N) (hx : w₁⁻¹ * w₂ = x) (hxN : x ∉ N)
    (hcov : ∀ g ∈ N, g ∈ J ∨ w₁⁻¹ * g ∈ J ∨ w₂⁻¹ * g ∈ J) :
    (∀ g ∈ N, g ∈ J ∨ w₁⁻¹ * g ∈ J) ∨ (∀ g ∈ N, g ∈ J ∨ w₂⁻¹ * g ∈ J) := by
  by_cases hex : ∃ b ∈ N, w₂⁻¹ * b ∈ J
  · right
    obtain ⟨b, hbN, hbJ⟩ := hex
    intro g hgN
    rcases hcov g hgN with hgJ | hgJ | hgJ
    · exact Or.inl hgJ
    · exfalso
      apply hxN
      have hkey : w₁⁻¹ * w₂ = (w₁⁻¹ * g) * (g⁻¹ * b) * (w₂⁻¹ * b)⁻¹ := by group
      rw [← hx, hkey]
      exact N.mul_mem (N.mul_mem (hJN hgJ) (N.mul_mem (N.inv_mem hgN) hbN))
        (N.inv_mem (hJN hbJ))
    · exact Or.inr hgJ
  · left
    intro g hgN
    rcases hcov g hgN with hgJ | hgJ | hgJ
    · exact Or.inl hgJ
    · exact Or.inr hgJ
    · exact absurd ⟨g, hgN, hgJ⟩ hex

theorem card_le_two_mul_of_subset_cosets [Finite P] {J N : Subgroup P} {w₁ w₂ x : P}
    (hJN : J ≤ N) (hx : w₁⁻¹ * w₂ = x) (hxN : x ∉ N)
    (hcov : ∀ g ∈ N, g ∈ J ∨ w₁⁻¹ * g ∈ J ∨ w₂⁻¹ * g ∈ J) :
    Nat.card ↥N ≤ 2 * Nat.card ↥J := by
  rcases covered_by_two hJN hx hxN hcov with h | h
  · exact card_le_two_mul_of_forall h
  · exact card_le_two_mul_of_forall h

end CFSG.EvenSporadicStandard.M12Std.Rbc
