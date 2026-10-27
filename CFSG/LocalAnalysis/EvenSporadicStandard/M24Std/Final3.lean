module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.FirstHalf
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LocalSettingOf

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem ega81Wreath_of_secondHalf
    (hHS : HarrisSolomonZ2S6IsoK) (h2 : Ega81Lemmas214to217) : Ega81Wreath := by
  intro hA G _ _ L hKS hZ hstd hsp hcyc hS hcase
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz, hz2⟩ : ∃ z : G, z ∈ centralizer (L : Set G) ∧ orderOf z = 2 := by
    obtain ⟨S₀⟩ : Nonempty (Sylow 2 (centralizer (L : Set G))) := inferInstance
    have hdvd : 2 ∣ Nat.card (centralizer (L : Set G)) := by
      rw [← hS S₀]
      exact Subgroup.card_subgroup_dvd_card (S₀ : Subgroup (centralizer (L : Set G)))
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  have hC := hcase z hz hz2
  have hcen : zpowers z ≤ centralizer (L : Set G) := (zpowers_le).2 hz
  have hd : Disjoint L (zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro x hxL hxz
    have hxc : x ∈ centralizer (L : Set G) := hcen hxz
    have hxcen : (⟨x, hxL⟩ : L) ∈ center L := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.1 hxc g g.2)
    rw [center_eq_bot_of_isSporadic_M24 hsp] at hxcen
    exact congrArg Subtype.val (mem_bot.1 hxcen)
  have hs := localSetting_of_centralizer_eq hz2 hcen hC.1 hd hsp
  obtain ⟨A', B, C, D, hFH⟩ := exists_firstHalf hs hC.2
  exact ⟨z, hz, hz2, h2 hA hHS G L z hKS hZ hstd hs A' B C D hFH⟩

end CFSG.EvenSporadicStandard.M24Std
