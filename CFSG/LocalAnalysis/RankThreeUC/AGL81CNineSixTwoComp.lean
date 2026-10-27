module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs

import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Two
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineSixStarEGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
import CFSG.LocalAnalysis.RankThreeUC.AGL81CThreeComponents
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenLayerGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineTenThreeGen
import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenCF
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenG1

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G} {p : ℕ}

private theorem starImg_component_facts (h : NineSettingGen G M p Q H E 2) {J : Subgroup G}
    (hJ : IsPComponentIn p J H) (hJM : ¬ J ≤ M) :
    CFSG.IsComponent (starImg p H J) ∧ ¬ starImg p H J ≤ starImg p H M ∧
      p ∣ Nat.card (starImg p H J) := by
  have hC : CFSG.IsComponent (starImg p H J) := isComponent_starImg hJ
  refine ⟨hC, fun hle => hJM ((h.le_iff_starImg_le hJ.1).mpr hle), ?_⟩
  exact CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card (p := p) h.prime
    (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.pPrimeCore_starGroup (H := H) h.prime) hC

theorem nineSixTwoComp_holds : NineSixTwoComp := by
  intro G _ _ M Q H E p h hH2 hp _
  by_contra hlt
  obtain ⟨J₁, J₂, J₃, hJ₁, hJ₂, hJ₃, h₁₂, h₁₃, h₂₃⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).mp (not_le.mp hlt)
  obtain ⟨hC₁, hC₁M, hd₁⟩ := starImg_component_facts h hJ₁.1 hJ₁.2
  obtain ⟨hC₂, hC₂M, hd₂⟩ := starImg_component_facts h hJ₂.1 hJ₂.2
  obtain ⟨hC₃, hC₃M, hd₃⟩ := starImg_component_facts h hJ₃.1 hJ₃.2
  have h4 := four_le_pRank_of_three_components h.prime h.ne_two hC₁ hC₂ hC₃
    (fun he => h₁₂ (eq_of_starImg_eq h.prime hJ₁.1 hJ₂.1 he))
    (fun he => h₁₃ (eq_of_starImg_eq h.prime hJ₁.1 hJ₃.1 he))
    (fun he => h₂₃ (eq_of_starImg_eq h.prime hJ₂.1 hJ₃.1 he)) hd₁ hd₂ hd₃
    h.isElemAbelian_starImg_E_gen h.card_starImg_E_gen
    (h.starImg_E_le_normalizer_gen hC₁ hC₁M) (h.starImg_E_le_normalizer_gen hC₂ hC₂M)
    (h.starImg_E_le_normalizer_gen hC₃ hC₃M)
    (fun _ hf hf1 => h.not_le_centralizer_of_mem_starImg_E_gen hC₁M hf hf1)
  have h3 := h.pRank_star_le_three hH2 hp
  omega

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
