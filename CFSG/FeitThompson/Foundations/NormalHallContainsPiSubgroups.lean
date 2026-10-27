module

public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Foundations.FiniteHomImageOrder
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex

open Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X] {π π' : Set ℕ}

structure IsHallPiSubgroup (π : Set ℕ) (H : Subgroup X) : Prop where
  isPiSubgroup : IsPiSubgroup π H
  notMem_of_mem_primeFactors_index : ∀ p ∈ H.index.primeFactors, p ∉ π

theorem isHallPiSubgroup_iff {H : Subgroup X} :
    IsHallPiSubgroup π H ↔
      (∀ p ∈ (Nat.card H).primeFactors, p ∈ π) ∧ ∀ p ∈ H.index.primeFactors, p ∉ π :=
  ⟨fun h => ⟨isPiSubgroup_iff.1 h.isPiSubgroup, h.notMem_of_mem_primeFactors_index⟩,
    fun h => ⟨isPiSubgroup_iff.2 h.1, h.2⟩⟩

theorem isHallPiSubgroup_iff_natCard_range_leftCoset {H : Subgroup X} :
    IsHallPiSubgroup π H ↔ IsPiSubgroup π H ∧
      ∀ p ∈ (Nat.card (Set.range fun g : X => g • (H : Set X))).primeFactors, p ∉ π := by
  rw [natCard_range_leftCoset]
  exact ⟨fun h => ⟨h.isPiSubgroup, h.notMem_of_mem_primeFactors_index⟩, fun h => ⟨h.1, h.2⟩⟩

theorem IsHallPiSubgroup.top (h : IsPiSubgroup π (⊤ : Subgroup X)) :
    IsHallPiSubgroup π (⊤ : Subgroup X) :=
  ⟨h, by simp⟩

theorem IsHallPiSubgroup.coprime_natCard_index [Finite X] {H : Subgroup X}
    (hH : IsHallPiSubgroup π H) : (Nat.card H).Coprime H.index := by
  by_contra hc
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.Prime.not_coprime_iff_dvd.1 hc
  exact hH.notMem_of_mem_primeFactors_index p
    (Nat.mem_primeFactors.2 ⟨hp, hp2, Subgroup.index_ne_zero_of_finite⟩)
    (isPiSubgroup_iff.1 hH.isPiSubgroup p (Nat.mem_primeFactors.2 ⟨hp, hp1, Nat.card_pos.ne'⟩))

theorem IsHallPiSubgroup.le_of_isPiSubgroup [Finite X] {H Y : Subgroup X} [H.Normal]
    (hH : IsHallPiSubgroup π H) (hY : IsPiSubgroup π Y) : Y ≤ H := by
  set f : Y →* X ⧸ H := (QuotientGroup.mk' H).comp Y.subtype with hf
  have h1 : Nat.card f.range ∣ Nat.card Y := Subgroup.card_range_dvd f
  have h2 : Nat.card f.range ∣ H.index := by
    rw [Subgroup.index_eq_card]
    exact natCard_range_dvd_natCard_codomain f
  have hempty : (Nat.card f.range).primeFactors = ∅ := by
    ext p
    simp only [Finset.notMem_empty, iff_false]
    intro hp
    exact hH.notMem_of_mem_primeFactors_index p
      (Nat.primeFactors_mono h2 Subgroup.index_ne_zero_of_finite hp)
      (isPiSubgroup_iff.1 hY p (Nat.primeFactors_mono h1 Nat.card_pos.ne' hp))
  have hone : Nat.card f.range = 1 := by
    rcases Nat.primeFactors_eq_empty.1 hempty with h | h
    · exact absurd h Nat.card_pos.ne'
    · exact h
  have hbot : f.range = ⊥ := Subgroup.card_eq_one.1 hone
  intro y hy
  have hmem : f ⟨y, hy⟩ ∈ f.range := ⟨_, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  simpa [hf, QuotientGroup.eq_one_iff] using hmem

theorem IsHallPiSubgroup.mem_iff [Finite X] {H : Subgroup X} [H.Normal]
    (hH : IsHallPiSubgroup π H) (x : X) :
    x ∈ H ↔ ∀ p ∈ (orderOf x).primeFactors, p ∈ π := by
  refine ⟨fun hx p hp => isPiSubgroup_iff.1 hH.isPiSubgroup p
    (Nat.primeFactors_mono (H.orderOf_dvd_natCard hx) Nat.card_pos.ne' hp), fun hx => ?_⟩
  refine hH.le_of_isPiSubgroup (isPiSubgroup_iff.2 fun p hp => hx p ?_) (Subgroup.mem_zpowers x)
  rwa [Nat.card_zpowers] at hp

theorem IsHallPiSubgroup.eq_piCore [Finite X] {H : Subgroup X} [H.Normal]
    (hH : IsHallPiSubgroup π H) : H = piCore π X :=
  le_antisymm (le_piCore ‹H.Normal› hH.isPiSubgroup) (piCore_le fun _ _ hπ => hH.le_of_isPiSubgroup hπ)

theorem IsHallPiSubgroup.unique [Finite X] {H K : Subgroup X} [H.Normal] [K.Normal]
    (hH : IsHallPiSubgroup π H) (hK : IsHallPiSubgroup π K) : H = K :=
  hH.eq_piCore.trans hK.eq_piCore.symm

theorem IsHallPiSubgroup.mono {H : Subgroup X} (hH : IsHallPiSubgroup π H) (hπ : π ⊆ π')
    (hπ' : ∀ p ∈ H.index.primeFactors, p ∉ π') : IsHallPiSubgroup π' H :=
  ⟨hH.isPiSubgroup.mono hπ, hπ'⟩

end

end CFSG.FeitThompson
