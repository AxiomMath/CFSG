module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalG

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup CFSG.Blueprint.NativeSporadic

theorem thCyc_of_core {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) {F : Subgroup G} {t : G} (hD : ThData ↥F)
    (ht : orderOf t = 2) (hC : centralizer ({t} : Set G) = F ⊔ zpowers t)
    (hnc : ∀ g : G, g⁻¹ * t * g ∉ F) : ThCyc G F (zpowers t) t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htF : t ∉ F := by simpa using hnc 1
  refine ⟨hs, hn, hD, mem_zpowers t, ht, ?_, inferInstance, ?_, hC, ?_⟩
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  · rw [zpowers_le]
    refine mem_centralizer_iff.2 fun f hf => ?_
    have : f ∈ centralizer ({t} : Set G) := by
      rw [hC]
      exact mem_sup_left hf
    exact mem_centralizer_singleton_iff.1 this
  · rw [disjoint_iff, eq_bot_iff]
    intro x hx
    obtain ⟨hxF, hxt⟩ := hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxt
    have h2 : t ^ 2 = 1 := by
      rw [← ht]
      exact pow_orderOf_eq_one t
    rcases zpow_eq_one_or_self h2 k with h | h
    · rw [h]
      exact one_mem _
    · rw [h] at hxF
      exact absurd hxF htF

end CFSG.EvenSporadicStandard.ThStd
