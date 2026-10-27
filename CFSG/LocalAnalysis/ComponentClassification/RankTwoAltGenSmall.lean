module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenSmallRoot
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenCent
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltOpenDefs

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical

namespace AltGenSetting

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}
  {Φ : alternatingGroup (Fin (n + 4)) →* G}

theorem rankTwoX_eq_small
    (s : AltGenSetting A R T g n Φ) (hn : n = 6 ∨ n = 7) (h34 : Asc08Lemma34)
    (hGA : Asc76X.GoldschmidtTheoremA) : rankTwoX A = A ⊔ rightConjugate A g :=
  s.rankTwoX_eq_of_local h34 (s.normalizer_le_small hn) (s.rootFusionAt_small hn)
    (s.typeTwoCentralizerAt_of hGA (s.normalizer_le_small hn) (s.rootFusionAt_small hn))

end AltGenSetting

theorem altGenerationSmall_of
    (h34 : Asc08Lemma34) (hGA : Asc76X.GoldschmidtTheoremA) : AltGenerationSmall :=
  fun _ _ _ _ _ _ _ _ _ hn s => s.rankTwoX_eq_small hn h34 hGA

end CFSG.ComponentClassification.RankTwoAlt
