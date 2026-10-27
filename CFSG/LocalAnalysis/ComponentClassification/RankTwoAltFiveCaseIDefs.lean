module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltOpenDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenY
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEIdent
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSmallFacts

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Subgroup CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical

@[expose] def AltGenerationFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R T : Subgroup G) (g : G)
    (Φ : alternatingGroup (Fin (5 + 4)) →* G), AltGenCore A R T g 5 Φ →
    rankTwoX A = A ⊔ rightConjugate A g

end CFSG.ComponentClassification.RankTwoAlt
