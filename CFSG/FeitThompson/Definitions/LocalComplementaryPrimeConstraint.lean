module

public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
public import Mathlib.Order.CompletePartialOrder

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G]

def subgroupPrimeSupport (A : Subgroup G) : Set ℕ := ↑(Nat.card A).primeFactors

def subgroupPrimeSupportCompl (A : Subgroup G) : Set ℕ :=
  {q : ℕ | q.Prime ∧ q ∉ subgroupPrimeSupport A}

theorem subgroupPrimeSupport_def (A : Subgroup G) :
    subgroupPrimeSupport A = ↑(Nat.card A).primeFactors := (rfl)

theorem mem_subgroupPrimeSupport_iff {A : Subgroup G} {p : ℕ} :
    p ∈ subgroupPrimeSupport A ↔ p ∈ (Nat.card A).primeFactors := (Iff.rfl)

theorem mem_subgroupPrimeSupportCompl_iff {A : Subgroup G} {q : ℕ} :
    q ∈ subgroupPrimeSupportCompl A ↔ q.Prime ∧ q ∉ subgroupPrimeSupport A := (Iff.rfl)

theorem prime_of_mem_subgroupPrimeSupport {A : Subgroup G} {p : ℕ}
    (hp : p ∈ subgroupPrimeSupport A) : p.Prime :=
  Nat.prime_of_mem_primeFactors (mem_subgroupPrimeSupport_iff.1 hp)

theorem subgroupPrimeSupportCompl_subset_setOf_prime (A : Subgroup G) :
    subgroupPrimeSupportCompl A ⊆ {q : ℕ | q.Prime } :=
  fun _ hq => (mem_subgroupPrimeSupportCompl_iff.1 hq).1

theorem disjoint_subgroupPrimeSupport_subgroupPrimeSupportCompl (A : Subgroup G) :
    Disjoint (subgroupPrimeSupport A) (subgroupPrimeSupportCompl A) :=
  Set.disjoint_left.2 fun _ hp hq => (mem_subgroupPrimeSupportCompl_iff.1 hq).2 hp

theorem subgroupPrimeSupport_eq_empty_iff [Finite G] {A : Subgroup G} :
    subgroupPrimeSupport A = ∅ ↔ A = ⊥ := by
  rw [subgroupPrimeSupport_def, Finset.coe_eq_empty, Nat.primeFactors_eq_empty]
  simp [Nat.card_pos.ne', Subgroup.card_eq_one]

theorem subgroupPrimeSupport_bot : subgroupPrimeSupport (⊥ : Subgroup G) = ∅ := by
  simp [subgroupPrimeSupport_def]

theorem subgroupPrimeSupportCompl_bot :
    subgroupPrimeSupportCompl (⊥ : Subgroup G) = {q : ℕ | q.Prime} := by
  ext q; simp [mem_subgroupPrimeSupportCompl_iff, subgroupPrimeSupport_bot]

theorem isPiSubgroup_subgroupPrimeSupport (A : Subgroup G) :
    IsPiSubgroup (subgroupPrimeSupport A) A :=
  isPiSubgroup_iff.2 fun _ hp => mem_subgroupPrimeSupport_iff.2 hp

theorem isPiSubgroup_map_subtype_iff {π : Set ℕ} {H : Subgroup G} {Y : Subgroup H} :
    IsPiSubgroup π (Y.map H.subtype) ↔ IsPiSubgroup π Y := by
  have h : Nat.card (Y.map H.subtype) = Nat.card Y :=
    (Nat.card_congr (Subgroup.equivMapOfInjective Y H.subtype H.subtype_injective).toEquiv).symm
  rw [isPiSubgroup_iff, isPiSubgroup_iff, h]

theorem inf_eq_bot_of_isPiSubgroup_subgroupPrimeSupportCompl [Finite G] {A Y : Subgroup G}
    (hY : IsPiSubgroup (subgroupPrimeSupportCompl A) Y) : A ⊓ Y = ⊥ := by
  have h1 := isPiSubgroup_iff.1 ((isPiSubgroup_subgroupPrimeSupport A).of_le (inf_le_left (b := Y)))
  have h2 := isPiSubgroup_iff.1 (hY.of_le (inf_le_right (a := A)))
  have h : (Nat.card (A ⊓ Y : Subgroup G)).primeFactors = ∅ := by
    ext p
    simp only [Finset.notMem_empty, iff_false]
    exact fun hp => (mem_subgroupPrimeSupportCompl_iff.1 (h2 p hp)).2 (h1 p hp)
  rcases Nat.primeFactors_eq_empty.1 h with h | h
  · exact absurd h Nat.card_pos.ne'
  · exact Subgroup.card_eq_one.1 h

def IsConstrained [Finite G] (A : Subgroup G) : Prop :=
  ∀ H : Subgroup G, H < ⊤ → A ≤ H → ∀ Y : Subgroup G, Y ≤ H →
    IsPiSubgroup (subgroupPrimeSupportCompl A) Y → A ≤ normalizer (Y : Set G) →
      Y ≤ (piCore (subgroupPrimeSupportCompl A) H).map H.subtype

theorem map_top_subtype (H : Subgroup G) : (⊤ : Subgroup H).map H.subtype = H := by
  rw [← Subgroup.subgroupOf_self H, Subgroup.map_subgroupOf_eq_of_le le_rfl]

variable [Finite G]

theorem isConstrained_iff {A : Subgroup G} :
    IsConstrained A ↔ ∀ H : Subgroup G, H < ⊤ → A ≤ H → ∀ Y : Subgroup G, Y ≤ H →
      IsPiSubgroup (subgroupPrimeSupportCompl A) Y → A ≤ normalizer (Y : Set G) →
        Y ≤ (piCore (subgroupPrimeSupportCompl A) H).map H.subtype := (Iff.rfl)

theorem IsConstrained.le_map_piCore {A : Subgroup G} (h : IsConstrained A) {H Y : Subgroup G}
    (hH : H < ⊤) (hAH : A ≤ H) (hYH : Y ≤ H) (hY : IsPiSubgroup (subgroupPrimeSupportCompl A) Y)
    (hN : A ≤ normalizer (Y : Set G)) :
    Y ≤ (piCore (subgroupPrimeSupportCompl A) H).map H.subtype :=
  h H hH hAH Y hYH hY hN

theorem le_map_piCore_iff (π : Set ℕ) {H Y : Subgroup G} (hY : Y ≤ H) :
    Y ≤ (piCore π H).map H.subtype ↔ Y.subgroupOf H ≤ piCore π H := by
  rw [← Subgroup.map_subtype_le_map_subtype, Subgroup.map_subgroupOf_eq_of_le hY]

theorem IsConstrained.subgroupOf_le_piCore {A : Subgroup G} (h : IsConstrained A)
    {H Y : Subgroup G} (hH : H < ⊤) (hAH : A ≤ H) (hYH : Y ≤ H)
    (hY : IsPiSubgroup (subgroupPrimeSupportCompl A) Y) (hN : A ≤ normalizer (Y : Set G)) :
    Y.subgroupOf H ≤ piCore (subgroupPrimeSupportCompl A) H :=
  (le_map_piCore_iff _ hYH).1 (h.le_map_piCore hH hAH hYH hY hN)

theorem isConstrained_iff_forall_subgroup {A : Subgroup G} :
    IsConstrained A ↔ ∀ H : Subgroup G, H < ⊤ → A ≤ H → ∀ Y : Subgroup H,
      IsPiSubgroup (subgroupPrimeSupportCompl A) Y →
      A ≤ normalizer ((Y.map H.subtype : Subgroup G) : Set G) →
        Y ≤ piCore (subgroupPrimeSupportCompl A) H := by
  constructor
  · intro h H hH hAH Y hY hN
    rw [← Subgroup.map_subtype_le_map_subtype]
    exact h H hH hAH _ (Subgroup.map_subtype_le Y) (isPiSubgroup_map_subtype_iff.2 hY) hN
  · intro h H hH hAH Y hYH hY hN
    rw [le_map_piCore_iff _ hYH]
    refine h H hH hAH (Y.subgroupOf H) (isPiSubgroup_map_subtype_iff.1 ?_) ?_
    · rwa [Subgroup.map_subgroupOf_eq_of_le hYH]
    · rwa [Subgroup.map_subgroupOf_eq_of_le hYH]

theorem isConstrained_top : IsConstrained (⊤ : Subgroup G) := fun _ hH hA _ _ _ _ =>
  absurd (top_le_iff.1 hA) hH.ne

theorem isConstrained_bot : IsConstrained (⊥ : Subgroup G) := by
  intro H _ _ Y hYH _ _
  have hpc : piCore (subgroupPrimeSupportCompl (⊥ : Subgroup G)) H = ⊤ := by
    rw [subgroupPrimeSupportCompl_bot]
    exact eq_top_iff.2 (le_piCore (Subgroup.normal_of_characteristic ⊤)
      (isPiSubgroup_iff.2 fun _ hp => Nat.prime_of_mem_primeFactors hp))
  rw [hpc, map_top_subtype]
  exact hYH

end

end CFSG.FeitThompson
