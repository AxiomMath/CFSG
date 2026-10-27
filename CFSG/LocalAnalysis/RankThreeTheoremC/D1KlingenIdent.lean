module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3K
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenIdentDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Rest3A6
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralAlpha

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type} [Group G] [Finite G]

theorem d1ConstrainedPhase3ResiduesK3_of_ident (h : KFactKlingenIdent) :
    D1ConstrainedPhase3ResiduesK3 G where
  klingen := d1CaseThreeKlingenOther3_of_ident h

structure D1FrontierResidues3L (G : Type) [Group G] [Finite G] : Prop where
  oneSmall : D1CaseOneSmall3 G
  twoCentral : D1CaseTwoCentral3Beta G
  twoRest : D1CaseTwoRest3A6 G

theorem D1FrontierResidues3L.toK (hid : KFactKlingenIdent)
    (hk : D1CaseTwoKFacts3 G) (hZ : CFSG.AGLEmbedding.KFactFixCensusCenter)
    (hgrp : CaseTwoGroupFacts) (hKF : KFactBlockFieldIndex) (h : D1FrontierResidues3L G) :
    D1FrontierResidues3K G where
  constrained := d1ConstrainedPhase3ResiduesK3_of_ident hid
  oneSmall := h.oneSmall
  twoCentral := d1CaseTwoCentral3_of_beta hk hgrp hKF h.twoCentral
  twoRest := d1CaseTwoRest3b_of_rest3A6 hk hZ h.twoRest

theorem d1FrontierResidues3L_of_frontier3K (h : D1FrontierResidues3K G) :
    D1FrontierResidues3L G where
  oneSmall := h.oneSmall
  twoCentral := d1CaseTwoCentral3Beta_of_central3 h.twoCentral
  twoRest := d1CaseTwoRest3A6_of_rest3b h.twoRest

theorem d1FrontierResidues3L_of_theoremD1 (hD1 : TheoremD1 G) : D1FrontierResidues3L G :=
  d1FrontierResidues3L_of_frontier3K (d1FrontierResidues3K_of_theoremD1 hD1)

end CFSG.LocalAnalysis.RankThreeTheoremC
