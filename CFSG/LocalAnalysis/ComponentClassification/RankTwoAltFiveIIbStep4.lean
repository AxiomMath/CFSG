module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbExclZ
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbFusion
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveIIbGood
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XMain

public section

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

namespace CFSG.ComponentClassification.RankTwoAltFive

theorem asc310IIbStep4_of (hGold : Asc76X.GoldschmidtTheoremA) :
    Asc310IIbStep4 := by
  intro G _ _ A R g T V₀ h hIIb
  obtain ⟨P, hP, hVP, hPC, hP64⟩ := h.exists_sylow_transv
  by_cases hm : MType (R ⊔ T) P
  · by_cases hε : EpsOne (R ⊔ T) P
    · exact (h.false_of_eps_one_mType hP hPC hIIb hGold hP64 hε hm).elim
    obtain ⟨x, z, r₁, hx⟩ := h.exists_outerInvol hP hPC hP64 hVP hε
    obtain ⟨f, hf⟩ := h.exists_iIbHom_of_mType hP hPC hx hm hP64
    exact ⟨P, x, z, r₁, f IIbSyl.sigma, f IIbSyl.c1, hP, hPC, hx,
      h.isSylowOf_top_of_mType hP hPC hx hm hP64,
      ⟨f, hf.inj, hf.range, h.map_S0_eq hP hPC hx hIIb hm hP64 hf, hf.mapP, hf.mapV0, hf.mapR,
        hf.t, hf.z0, hf.a, rfl, rfl⟩,
      h.sigma_conj_of_hom' hx hIIb hf.inj hf.range hf.mapV0 hf.mapV hf.a hf.sigma_mem
        hf.sigma_ne_one hf.sigma_ne_r,
      h.outer_not_isConj hP hPC hx hIIb hm hP64 hf,
      h.mul_self_mem_of_centralizer hP hPC hm hP64⟩
  ·
    obtain ⟨V', hV'⟩ : ∃ V' : Subgroup G, IsVprime (R ⊔ T) V₀ P V' := by
      unfold MType at hm
      push Not at hm
      obtain ⟨c₁, hc₁, c₂, hc₂, hc₁V, hc₂V, hc₁2, hc₂2, hc₁₂, hcomm⟩ := hm
      exact h.exists_isVprime_of_comm hP hPC hP64 hc₁ hc₁V hc₁2 hc₂ hc₂V hc₂2 hc₁₂ hcomm
    by_cases hε : EpsOne (R ⊔ T) P
    · by_cases hcase : ∀ c ∈ V', c ∉ V₀ → ∀ w ∈ V₀, w ≠ 1 → ¬ IsConj w c
      · exact (h.false_of_eps_one_isVprime_of_not_conj hP hPC hIIb hGold hP64 hε hV'
          hcase).elim
      · push Not at hcase
        obtain ⟨c, hcV', hcV₀, w, hw, hw1, hwc⟩ := hcase
        exact (h.false_of_eps_one_isVprime_of_conj hP hPC hIIb hGold hP64 hε hV' hcV' hcV₀ hw
          hw1 hwc).elim
    · obtain ⟨x, z, r₁, hx⟩ := h.exists_outerInvol hP hPC hP64 hVP hε
      exact (h.false_of_outer_isVprime hP hPC hIIb hx hV' hGold hP64).elim

theorem asc310IIbStep4 :
    Asc310IIbStep4 :=
  asc310IIbStep4_of Asc76X.goldschmidtTheoremA

end CFSG.ComponentClassification.RankTwoAltFive
