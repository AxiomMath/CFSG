module

public import CFSG.FeitThompson.Definitions.ConventionForPLengthAtMostOne
public import CFSG.FeitThompson.Definitions.NarrowPGroupsAndBetaPrimes
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Local.ElementaryMaximalPLengthOneConstraint
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
theorem odd_of_ne_bot_of_isPGroup (hoddG : Odd (Nat.card G)) (hp : p.Prime) {A : Subgroup G}
    (hA : A ≠ ⊥) (hAp : IsPGroup p A) : Odd p := by
  have := Fact.mk hp
  have hpdvd : p ∣ Nat.card A := by
    rcases hAp.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hA
    · exact h
  exact hoddG.of_dvd_nat (hpdvd.trans (Subgroup.card_subgroup_dvd_card A))

theorem lt_top_of_maximal_isElementaryAbelianSubgroup [IsSimpleGroup G]
    (hG : ¬ IsMulCommutative G) (hp : p.Prime) {A : Subgroup G} (hA0 : A ≠ ⊥)
    (hA : Maximal (IsElementaryAbelianSubgroup p) A) : A < ⊤ :=
  lt_top_of_isPGroup hG hp hA0 hA.prop.isPGroup

theorem le_pComplCore_of_maximal_of_le_normalizer (hoddG : Odd (Nat.card G))
    (hp : p.Prime) {A : Subgroup G} (hA0 : A ≠ ⊥)
    (hA : Maximal (IsElementaryAbelianSubgroup p) A) {X : Subgroup G}
    (hXsolv : Group.IsSolvable X) (hXlen : HasPLengthLeOne p X) (hAX : A ≤ X) {Y : Subgroup X}
    (hY : p.Coprime (Nat.card Y)) (hAY : A.subgroupOf X ≤ normalizer (Y : Set X)) :
    Y ≤ pComplCore p X :=
  have := hXsolv
  le_pComplCore_of_maximal_isElementaryAbelianSubgroup hp
    (odd_of_ne_bot_of_isPGroup hoddG hp hA0 hA.prop.isPGroup) hXlen
    (maximal_isElementaryAbelianSubgroup_subgroupOf hA hAX) hY hAY

theorem subgroupOf_le_pComplCore_of_maximal_of_le_normalizer (hoddG : Odd (Nat.card G))
    (hp : p.Prime) {A : Subgroup G} (hA0 : A ≠ ⊥)
    (hA : Maximal (IsElementaryAbelianSubgroup p) A) {X : Subgroup G}
    (hXsolv : Group.IsSolvable X) (hXlen : HasPLengthLeOne p X) (hAX : A ≤ X) {Y : Subgroup G}
    (hYX : Y ≤ X) (hY : p.Coprime (Nat.card Y)) (hAY : A ≤ normalizer (Y : Set G)) :
    Y.subgroupOf X ≤ pComplCore p X := by
  refine le_pComplCore_of_maximal_of_le_normalizer hoddG hp hA0 hA hXsolv hXlen hAX ?_ ?_
  · rwa [Nat.card_congr (subgroupOfEquivOfLe hYX).toEquiv]
  · intro a ha
    exact le_normalizer_comap X.subtype (show a ∈ (normalizer (Y : Set G)).comap X.subtype from
      hAY (mem_subgroupOf.1 ha))

theorem le_map_pComplCore_of_maximal_of_le_normalizer (hoddG : Odd (Nat.card G))
    (hp : p.Prime) {A : Subgroup G} (hA0 : A ≠ ⊥)
    (hA : Maximal (IsElementaryAbelianSubgroup p) A) {X : Subgroup G}
    (hXsolv : Group.IsSolvable X) (hXlen : HasPLengthLeOne p X) (hAX : A ≤ X) {Y : Subgroup G}
    (hYX : Y ≤ X) (hY : p.Coprime (Nat.card Y)) (hAY : A ≤ normalizer (Y : Set G)) :
    Y ≤ (pComplCore p X).map X.subtype := fun y hy =>
  ⟨⟨y, hYX hy⟩, subgroupOf_le_pComplCore_of_maximal_of_le_normalizer hoddG hp hA0 hA hXsolv
    hXlen hAX hYX hY hAY (mem_subgroupOf.2 hy), rfl⟩

theorem lt_top_and_forall_subgroupOf_le_pComplCore [IsSimpleGroup G] (hoddG : Odd (Nat.card G))
    (hG : ¬ IsMulCommutative G) (hsolv : ∀ H : Subgroup G, H < ⊤ → Group.IsSolvable H)
    (hp : p.Prime) {A : Subgroup G} (hA0 : A ≠ ⊥)
    (hA : Maximal (IsElementaryAbelianSubgroup p) A)
    (hlen : ∀ H : Subgroup G, H < ⊤ → HasPLengthLeOne p H) :
    A < ⊤ ∧ ∀ X : Subgroup G, X < ⊤ → A ≤ X → ∀ Y : Subgroup G, Y ≤ X →
      p.Coprime (Nat.card Y) → A ≤ normalizer (Y : Set G) → Y.subgroupOf X ≤ pComplCore p X :=
  ⟨lt_top_of_maximal_isElementaryAbelianSubgroup hG hp hA0 hA,
    fun X hX hAX _Y hYX hY hAY => subgroupOf_le_pComplCore_of_maximal_of_le_normalizer hoddG hp
      hA0 hA (hsolv X hX) (hlen X hX) hAX hYX hY hAY⟩

end

end CFSG.FeitThompson
