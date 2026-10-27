module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Endgame

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open

section Step26


theorem step26_holds : Step26 := by
  intro G _ _ d z₀ h49 hd hz h22 h23a h25 S hS
  obtain ⟨hfusS, hsyl⟩ := h25 S hS
  have htS : d.t ∈ S := by
    have h1 : d.t ∈ d.tG ∩ (S : Set G) := by
      rw [hfusS]
      exact ⟨1, S.one_mem, by simp⟩
    exact h1.2
  have hfus : ∀ g : G, g⁻¹ * d.t * g ∈ S → ∃ s ∈ S, g⁻¹ * d.t * g = s⁻¹ * d.t * s := by
    intro g hg
    have h1 : g⁻¹ * d.t * g ∈ d.tG ∩ (S : Set G) :=
      ⟨⟨g⁻¹, by simp⟩, hg⟩
    rw [hfusS] at h1
    obtain ⟨s, hs, hsg⟩ := h1
    exact ⟨s⁻¹, S.inv_mem hs, by rw [← hsg]; simp⟩
  have hSH : fusionIsSylowIn 2 S (Hg d) := (h22 S hS).2.1
  have hH₀H : H0 d z₀ ≤ Hg d := inf_le_left
  obtain ⟨hN, hquot⟩ := h23a.2.2.2.2.1
  have hnorm : Hg d ≤ normalizer ((H0 d z₀ : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH₀H).mp hN
  have hidx : (H0 d z₀).relIndex (Hg d) = 2 ∨ (H0 d z₀).relIndex (Hg d) = 6 := by
    haveI := hN
    exact P6.relIndex_eq_two_or_six hquot
  exact P6.firstTransferData_of_sylow_quotient hd.t_two hSH hH₀H hnorm hidx h23a.2.2.2.1 htS hfus hsyl

end Step26

end CFSG.LocalAnalysis.EvenBN.Tits.N
