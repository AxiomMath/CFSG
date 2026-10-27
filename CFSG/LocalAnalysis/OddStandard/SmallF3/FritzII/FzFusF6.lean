module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzFusLet

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup Certificates.FzJ36 Certificates.FzFus

variable {G : Type} [Group G]

theorem fzfus_pairAtR : FzPairAtR := by
  intro G _ _ t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ hs ht h1 h2 h12 i hi hi2 hiZ
  obtain ⟨π, hd⟩ := fzfus_dict hs ht h1 h2 h12
  obtain ⟨⟨q1, q2, q3⟩, rfl⟩ := hd.mem_fzR6_iff.mp hi
  obtain ⟨-, hl1, hl2, hl3⟩ := fzfus_letters hd h12 hi2 hiZ
  obtain ⟨hc1, hc2, hd5⟩ := pairR_fact q1 q2 q3 hl1 hl2 hl3
  refine ⟨π (mkE q1 1 1), hd.mem_T₂_iff.mpr ⟨mkE q1 1 1, rfl⟩,
    π (mkE 1 q2 1), hd.mem_T₂_iff.mpr ⟨mkE 1 q2 1, rfl⟩, ?_, ?_, hd.distinct5_iff.mp hd5⟩
  · have h := (hd.eq_iff (mkE q1 1 1 * mkE q1 q2 q3) (mkE q1 q2 q3 * mkE q1 1 1)).mpr hc1
    rwa [map_mul, map_mul] at h
  · have h := (hd.eq_iff (mkE 1 q2 1 * mkE q1 q2 q3) (mkE q1 q2 q3 * mkE 1 q2 1)).mpr hc2
    rwa [map_mul, map_mul] at h

theorem fzfus_noPairAtZ3 (hN : Pair7Fact) : FzNoPairAtZ3 := by
  intro G _ _ t x₁ x₂ lam T₂ a₁₂ a₂₂ a₃₂ hs ht h1 h2 h12 a ha b hb hD
  obtain ⟨π, hd⟩ := fzfus_dict hs ht h1 h2 h12
  obtain ⟨ma, rfl⟩ := hd.mem_T₂_iff.mp ha
  obtain ⟨mb, rfl⟩ := hd.mem_T₂_iff.mp hb
  rw [← hd.z3M_eq] at hD
  exact hN ma mb ((hd.distinct5_iff).mpr hD)

end CFSG.OddStandard.SmallF3.FritzII
