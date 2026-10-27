module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterRestRegular
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterRestEight
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterRestUntwist
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterRestCentral

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

section Certificates

theorem u3C1OuterLevelHighRestInput_holds : U3C1OuterLevelHighRestInput := by
  intro G _ _ L f t T R₂ D d V k H hC hk
  have hc := H.conf
  have h := H.start
  have hS2 := H.card_sylow
  have htrY := H.outerRest_transitive hk
  have htrE : ∀ b ∈ szA₁ (szT₁ L T), ∃ x ∈ normalizer (szR (szT₁ L T) V t : Set G) ⊓
      centralizer (szA₁ (szT₁ L T) : Set G), outerRestPt t k x = b := by
    by_cases hf : f = 3
    · exact hc.outerRest_exists_centralizing_of_eight h hS2 hk hf htrY
    · exact hc.outerRest_exists_centralizing_of_ne_three h hS2 hk hC.toU3C1Cartan hf htrY
  have htrU := hc.outerRest_exists_u3C1U_of_transitive h hS2 hk hC.toU3C1Cartan htrE
  obtain ⟨U₁, hU₁U, hUU₁, hsup, htU₁, hinf, hDU₁, hTU₁, -⟩ := hc.outerRest_exists_U₁ h hS2 hk hC
  exact ⟨hc.outerRest_isSylowOf h hS2 hk htrU, hc.outerRest_card_u3C1U h hS2 hk htrU, U₁, hU₁U,
    hUU₁, hsup, htU₁, hinf, hDU₁, hTU₁,
    hc.outerRest_conj_V₁ h hS2 hk hC.toU3C1Cartan htrU hU₁U hUU₁ hsup hinf (hDU₁ hC.mem)⟩

theorem u3C1NcycSylowStageInput_of_muOne (hM1 : U3C1OuterMuOneInput)
    (hM1S : U3C1OuterMuOneSylowInput) : U3C1NcycSylowStageInput :=
  u3C1NcycSylowStageInput_of_rest u3C1OuterLevelHighRestInput_holds hM1 hM1S

end Certificates

end CFSG.SeitzReduction.RankOne
