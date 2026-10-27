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

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedGS.AHelpers

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem le_normalizer_of_commutator_le {A B C : Subgroup G} (hcomm : ⁅A, B⁆ ≤ C) (hCB : C ≤ B) :
    A ≤ normalizer (B : Set G) := by
  have key : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ B :=
      hCB (hcomm (commutator_mem_commutator ha hb))
    have : a * b * a⁻¹ = a * b * a⁻¹ * b⁻¹ * b := by group
    rw [this]
    exact B.mul_mem hc hb
  intro a ha
  rw [mem_normalizer_iff]
  intro b
  constructor
  · exact key a ha b
  · intro hb
    have := key a⁻¹ (A.inv_mem ha) _ hb
    simpa [mul_assoc] using this

theorem card_sup_mul_card_inf [Finite G] (A B : Subgroup G) (h : B ≤ normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) =
      Nat.card A * Nat.card B := by
  have hrel := relIndex_mul_card A B
  have hrel' := relIndex_mul_card A (A ⊔ B)
  rw [inf_eq_left.mpr le_sup_left] at hrel'
  have hN : (A.subgroupOf (B ⊔ A)).Normal := normal_subgroupOf_sup_of_le_normalizer h
  have hN' : (A.subgroupOf B).Normal := normal_subgroupOf_of_le_normalizer h
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient B A h
  have hidx : A.relIndex B = A.relIndex (A ⊔ B) := by
    rw [relIndex, relIndex, index, index, sup_comm]
    exact (Nat.card_congr e.toEquiv)
  rw [← hrel', ← hrel, hidx, inf_comm]
  ring

theorem zpow_mem_iff_even {K : Subgroup G} {g : G} (hg : g ∉ K) (hg2 : g ^ 2 ∈ K) (k : ℤ) :
    g ^ k ∈ K ↔ Even k := by
  have hsq : ∀ q : ℤ, g ^ (2 * q) ∈ K := by
    intro q
    rw [zpow_mul]
    exact K.zpow_mem (by exact_mod_cast hg2) q
  rcases Int.even_or_odd k with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · refine ⟨fun _ => ⟨q, rfl⟩, fun _ => ?_⟩
    rw [← two_mul]
    exact hsq q
  · refine ⟨fun h => ?_, fun h => absurd h (Int.not_even_iff_odd.mpr ⟨q, rfl⟩)⟩
    exfalso
    apply hg
    have : g = (g ^ (2 * q))⁻¹ * g ^ (2 * q + 1) := by
      rw [zpow_add_one]; group
    rw [this]
    exact K.mul_mem (K.inv_mem (hsq q)) h

theorem mem_sup_zpowers_iff {B : Subgroup G} {g : G} (hgN : g ∈ normalizer (B : Set G))
    (hg : g ∉ B) (hg2 : g ^ 2 ∈ B) (x : G) :
    x ∈ B ⊔ zpowers g ↔ x ∈ B ∨ ∃ b ∈ B, x = b * g := by
  have hle : zpowers g ≤ normalizer (B : Set G) := zpowers_le.mpr hgN
  constructor
  · intro hx
    have hx' : x ∈ ((B ⊔ zpowers g : Subgroup G) : Set G) := hx
    rw [coe_mul_of_right_le_normalizer_left B (zpowers g) hle] at hx'
    obtain ⟨b, hb, y, hy, rfl⟩ := hx'
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rcases Int.even_or_odd k with hk | hk
    · left
      exact B.mul_mem hb ((zpow_mem_iff_even hg hg2 k).mpr hk)
    · right
      refine ⟨b * g ^ (k - 1), B.mul_mem hb ((zpow_mem_iff_even hg hg2 _).mpr ?_), ?_⟩
      · exact hk.sub_odd odd_one
      · rw [mul_assoc, ← zpow_add_one, sub_add_cancel]
  · rintro (hx | ⟨b, hb, rfl⟩)
    · exact mem_sup_left hx
    · exact mul_mem (mem_sup_left hb) (mem_sup_right (mem_zpowers g))

theorem relIndex_sup_zpowers_eq_two {B : Subgroup G} {g : G} (hgN : g ∈ normalizer (B : Set G))
    (hg : g ∉ B) (hg2 : g ^ 2 ∈ B) : B.relIndex (B ⊔ zpowers g) = 2 := by
  rw [relIndex_eq_two_iff]
  refine ⟨g, mem_sup_right (mem_zpowers g), fun x hx => ?_⟩
  rcases (mem_sup_zpowers_iff hgN hg hg2 x).mp hx with hxB | ⟨b, hb, rfl⟩
  · refine Or.inr ⟨hxB, fun h => hg ?_⟩
    have : g = x⁻¹ * (x * g) := by group
    rw [this]
    exact B.mul_mem (B.inv_mem hxB) h
  · refine Or.inl ⟨?_, fun h => hg ?_⟩
    · rw [mul_assoc, ← sq]
      exact B.mul_mem hb hg2
    · have : g = b⁻¹ * (b * g) := by group
      rw [this]
      exact B.mul_mem (B.inv_mem hb) h

theorem card_sup_zpowers_eq_two_mul {B : Subgroup G} {g : G} (hgN : g ∈ normalizer (B : Set G))
    (hg : g ∉ B) (hg2 : g ^ 2 ∈ B) : Nat.card (B ⊔ zpowers g : Subgroup G) = 2 * Nat.card B := by
  have h := relIndex_mul_card B (B ⊔ zpowers g)
  rw [inf_eq_left.mpr le_sup_left, relIndex_sup_zpowers_eq_two hgN hg hg2] at h
  exact h.symm

theorem card_subgroupOf_of_le {H K : Subgroup G} (h : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H :=
  Nat.card_congr (subgroupOfEquivOfLe h).toEquiv

end CFSG.ComponentClassification.UnbalancedGS.AHelpers
