module

public import Mathlib.GroupTheory.Sylow
public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Foundations.ProductSubgroupsCardinality

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {G : Type*} [Group G] {π : Set ℕ} {m n : ℕ}

def IsPiNumber (π : Set ℕ) (n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ∈ π

theorem isPiNumber_iff : IsPiNumber π n ↔ ∀ p ∈ n.primeFactors, p ∈ π := (Iff.rfl)

theorem isPiNumber_iff_of_ne_zero (hn : n ≠ 0) :
    IsPiNumber π n ↔ ∀ p : ℕ, p.Prime → p ∣ n → p ∈ π := by
  simp [IsPiNumber, Nat.mem_primeFactors, hn]

theorem isPiNumber_compl_iff : IsPiNumber πᶜ n ↔ ∀ p ∈ n.primeFactors, p ∉ π := (Iff.rfl)

@[simp]
theorem isPiNumber_one : IsPiNumber π 1 := by simp [IsPiNumber]

theorem isPiNumber_univ : IsPiNumber Set.univ n := fun _ _ => Set.mem_univ _

theorem IsPiNumber.mono {π' : Set ℕ} (h : IsPiNumber π n) (hπ : π ⊆ π') : IsPiNumber π' n :=
  fun p hp => hπ (h p hp)

theorem IsPiNumber.of_dvd (h : IsPiNumber π n) (hmn : m ∣ n) (hn : n ≠ 0) : IsPiNumber π m :=
  fun p hp => h p (Nat.primeFactors_mono hmn hn hp)

theorem IsPiNumber.mul (hm : IsPiNumber π m) (hn : IsPiNumber π n) : IsPiNumber π (m * n) := by
  rcases eq_or_ne m 0 with rfl | hm0
  · simp [IsPiNumber]
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [IsPiNumber]
  intro p hp
  rw [Nat.primeFactors_mul hm0 hn0] at hp
  rcases Finset.mem_union.1 hp with hp | hp
  · exact hm p hp
  · exact hn p hp

theorem IsPiNumber.eq_one_of_compl (h : IsPiNumber π n) (h' : IsPiNumber πᶜ n) (hn : n ≠ 0) :
    n = 1 := by
  have hempty : n.primeFactors = ∅ := by
    ext p
    simp only [Finset.notMem_empty, iff_false]
    exact fun hp => h' p hp (h p hp)
  rcases Nat.primeFactors_eq_empty.1 hempty with h | h
  · exact absurd h hn
  · exact h

theorem IsPiNumber.coprime_of_compl (h : IsPiNumber π m) (h' : IsPiNumber πᶜ n) (hm : m ≠ 0)
    (hn : n ≠ 0) : Nat.Coprime m n :=
  (Nat.disjoint_primeFactors hm hn).1 (Finset.disjoint_left.2 fun p hp hp' => h' p hp' (h p hp))

theorem isPiSubgroup_iff_isPiNumber {N : Subgroup G} :
    IsPiSubgroup π N ↔ IsPiNumber π (Nat.card N) :=
  isPiSubgroup_iff.trans isPiNumber_iff.symm

structure IsHallSubgroup (π : Set ℕ) (H : Subgroup G) : Prop where
  natCard : IsPiNumber π (Nat.card H)
  index : IsPiNumber πᶜ H.index

theorem index_eq_natCard_div_natCard [Finite G] (H : Subgroup G) :
    H.index = Nat.card G / Nat.card H := by
  rw [← Subgroup.card_mul_index H, Nat.mul_div_cancel_left _ Nat.card_pos]

theorem isHallSubgroup_iff {H : Subgroup G} :
    IsHallSubgroup π H ↔ IsPiNumber π (Nat.card H) ∧ IsPiNumber πᶜ H.index :=
  ⟨fun h => ⟨h.natCard, h.index⟩, fun h => ⟨h.1, h.2⟩⟩

theorem IsHallSubgroup.isPiSubgroup {H : Subgroup G} (hH : IsHallSubgroup π H) :
    IsPiSubgroup π H := isPiSubgroup_iff_isPiNumber.2 hH.natCard

theorem IsHallSubgroup.coprime_natCard_index [Finite G] {H : Subgroup G}
    (hH : IsHallSubgroup π H) : Nat.Coprime (Nat.card H) H.index :=
  hH.natCard.coprime_of_compl hH.index Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite

theorem isHallSubgroup_top_iff :
    IsHallSubgroup π (⊤ : Subgroup G) ↔ IsPiNumber π (Nat.card G) := by
  simp [isHallSubgroup_iff]

theorem isHallSubgroup_bot_iff :
    IsHallSubgroup π (⊥ : Subgroup G) ↔ IsPiNumber πᶜ (Nat.card G) := by
  simp [isHallSubgroup_iff]

theorem isHallSubgroup_sylow [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    IsHallSubgroup ({p} : Set ℕ) (P : Subgroup G) where
  natCard :=
    isPiSubgroup_iff_isPiNumber.1 ((isPiSubgroup_singleton_iff Fact.out _).2 P.isPGroup')
  index := by
    intro q hq hq'
    rw [Set.mem_singleton_iff] at hq'
    subst hq'
    exact P.not_dvd_index (Nat.dvd_of_mem_primeFactors hq)

theorem IsHallSubgroup.normal_le [Finite G] {N H : Subgroup G} [N.Normal]
    (hN : IsPiNumber π (Nat.card N)) (hH : IsHallSubgroup π H) : N ≤ H := by
  have hcard : Nat.card (H ⊔ N : Subgroup G) * Nat.card (H ⊓ N : Subgroup G)
      = Nat.card H * Nat.card N := by
    have hset : Nat.card ((H : Set G) * (N : Set G)) = Nat.card (H ⊔ N : Subgroup G) :=
      Nat.card_congr (Set.equivOfEq (Subgroup.mul_normal H N).symm)
    rw [← hset]
    exact natCard_mul_mul_natCard_inf H N
  obtain ⟨r, hr⟩ : Nat.card H ∣ Nat.card (H ⊔ N : Subgroup G) :=
    Subgroup.card_dvd_of_le le_sup_left
  have hkey : r * Nat.card (H ⊓ N : Subgroup G) = Nat.card N := by
    rw [hr, mul_assoc] at hcard
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hcard
  have hrN : r ∣ Nat.card N := ⟨_, hkey.symm⟩
  have hindex : H.index = r * (H ⊔ N : Subgroup G).index := by
    have h1 : Nat.card H * H.index = Nat.card G := Subgroup.card_mul_index H
    have h2 : Nat.card (H ⊔ N : Subgroup G) * (H ⊔ N : Subgroup G).index = Nat.card G :=
      Subgroup.card_mul_index _
    rw [hr, mul_assoc] at h2
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  have hrne : r ≠ 0 := by
    intro h
    rw [h, mul_zero] at hr
    exact Nat.card_pos.ne' hr
  have hr1 : r = 1 :=
    (hN.of_dvd hrN Nat.card_pos.ne').eq_one_of_compl
      (hH.index.of_dvd ⟨_, hindex⟩ Subgroup.index_ne_zero_of_finite) hrne
  have hsup : H = H ⊔ N :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hr, hr1, mul_one])
  exact hsup ▸ le_sup_right

theorem IsHallSubgroup.le_of_isPiSubgroup [Finite G] {N H : Subgroup G} [N.Normal]
    (hN : IsPiSubgroup π N) (hH : IsHallSubgroup π H) : N ≤ H :=
  hH.normal_le (isPiSubgroup_iff_isPiNumber.1 hN)

theorem IsHallSubgroup.piCore_le [Finite G] {H : Subgroup G} (hH : IsHallSubgroup π H) :
    piCore π G ≤ H :=
  CFSG.FeitThompson.piCore_le fun _ hN hπ =>
    haveI := hN
    hH.le_of_isPiSubgroup hπ

end CFSG.FeitThompson
