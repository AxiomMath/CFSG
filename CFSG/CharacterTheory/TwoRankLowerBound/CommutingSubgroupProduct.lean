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
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

open scoped Classical

namespace CFSG.TwoRankLowerBound.Helpers

@[expose] def commutingSubgroupProduct {G : Type*} [Group G] (left right : Subgroup G)
    (hcommute : ∀ first : left, ∀ second : right, Commute (first : G) (second : G)) :
    left × right →* G := left.subtype.noncommCoprod right.subtype hcommute

theorem commutingSubgroupProduct_injective {G : Type*} [Group G] (left right : Subgroup G)
    (hcommute : ∀ first : left, ∀ second : right, Commute (first : G) (second : G))
    (hdisjoint : Disjoint left right) : Function.Injective (commutingSubgroupProduct left right hcommute) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm
  · intro element hkernel
    have hone : (element.1 : G) * (element.2 : G) = 1 := hkernel
    obtain ⟨hleft, hright⟩ := Subgroup.disjoint_iff_mul_eq_one.mp hdisjoint
      element.1.property element.2.property hone
    rw [Subgroup.mem_bot]
    apply Prod.ext
    · exact Subtype.ext hleft
    · exact Subtype.ext hright
  · exact bot_le

@[expose] noncomputable def commutingSubgroupProductEquiv {G : Type*} [Group G] (left right : Subgroup G)
    (hcommute : ∀ first : left, ∀ second : right, Commute (first : G) (second : G))
    (hdisjoint : Disjoint left right) : left × right ≃* (commutingSubgroupProduct left right hcommute).range :=
  MulEquiv.ofBijective (commutingSubgroupProduct left right hcommute).rangeRestrict
    ⟨fun _ _ hequal => commutingSubgroupProduct_injective left right hcommute hdisjoint
      (congrArg Subtype.val hequal), MonoidHom.rangeRestrict_surjective _⟩

theorem commutingSubgroupProductEquiv_apply {G : Type*} [Group G] (left right : Subgroup G)
    (hcommute : ∀ first : left, ∀ second : right, Commute (first : G) (second : G))
    (hdisjoint : Disjoint left right) (element : left × right) :
    (commutingSubgroupProductEquiv left right hcommute hdisjoint element : G) =
      (element.1 : G) * (element.2 : G) := rfl

theorem commutingSubgroupProduct_card {G : Type*} [Group G] [Finite G] (left right : Subgroup G)
    (hcommute : ∀ first : left, ∀ second : right, Commute (first : G) (second : G))
    (hdisjoint : Disjoint left right) :
    Nat.card (commutingSubgroupProduct left right hcommute).range = Nat.card left * Nat.card right := by
  rw [← Nat.card_congr (commutingSubgroupProductEquiv left right hcommute hdisjoint).toEquiv, Nat.card_prod]

theorem prime_regular_centralizer_commuting_product {G : Type*} [Group G] [Finite G]
    (element : G) (prime : ℕ) [Fact (Nat.Prime prime)] (hregular : Nat.Coprime prime (orderOf element))
    (sylow : Sylow prime (Subgroup.centralizer ({element} : Set G))) :
    let cyclic := Subgroup.zpowers element
    let primary := (sylow : Subgroup (Subgroup.centralizer ({element} : Set G))).map
      (Subgroup.centralizer ({element} : Set G)).subtype
    (∀ first : cyclic, ∀ second : primary, Commute (first : G) (second : G)) ∧ Disjoint cyclic primary := by
  intro cyclic primary
  have hcommute : ∀ first : cyclic, ∀ second : primary, Commute (first : G) (second : G) := by
    intro first second
    obtain ⟨power, hpower⟩ := Subgroup.mem_zpowers_iff.mp first.property
    obtain ⟨member, _, hequal⟩ := second.property
    have hcommutes : Commute element (member : G) :=
      Subgroup.mem_centralizer_iff.mp member.property element (Set.mem_singleton _)
    change Commute (first : G) (second : G)
    rw [← hpower, ← hequal]
    exact hcommutes.zpow_left power
  refine ⟨hcommute, ?_⟩
  apply Subgroup.disjoint_of_coprime_natCard
  have hprimaryCard : Nat.card primary = prime ^ (Nat.card (Subgroup.centralizer ({element} : Set G))).factorization prime := by
    rw [Subgroup.card_map_of_injective (Subgroup.centralizer ({element} : Set G)).subtype_injective,
      Sylow.card_eq_multiplicity]
  rw [hprimaryCard, Nat.card_zpowers]
  exact hregular.symm.pow_right _

end CFSG.TwoRankLowerBound.Helpers
