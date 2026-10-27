module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Fine
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedNext3Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenThreeDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Rest3b
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenFiveDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenFiveMain

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

variable {G : Type} [Group G] [Finite G]

open CFSG.AGLEmbedding (Asc81bEightFive Asc81bEightFour Asc81bEightSix Asc81bNineThree
  AschbacherLocalCGTBlock CitedBlockThreeTransvection D1NoXBlock KFactBlockThreeAltSeven
  KFactBlockThreeOneOrbit KFactOutElemRank KFactParabolicThree)

structure D1ConstrainedPhase3ResiduesK3 (G : Type) [Group G] [Finite G] : Prop where
  klingen : D1CaseThreeKlingenOther3 G

theorem D1ConstrainedPhase3ResiduesK3.toResidues3 (hK : KFactBlockPerfectCoreThree)
    (hK5 : KFactBlockSylowThreeAut) (hK6 : KFactBlockHeisenbergAut) (hOut : KFactOutElemRank)
    (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hmod : StmtKlingenModel) (hsp : KFactKlingenLocal) (hsp3 : KFactKlingenThreeLocal)
    (hsp5 : KFactKlingenFiveLocal) (hK7 : KFactBlockHeisenbergInner)
    (hβ : KFactBetaRank2) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix)
    (hPar : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hAlt : KFactBlockThreeAltSeven) (hOne : KFactBlockThreeOneOrbit)
    (hCGT : AschbacherLocalCGTBlock) (h1s : D1CaseOneSmall3 G) (h2 : D1CaseTwo3 G)
    (h3 : D1CaseThreeNotKlingen3 G) (h : D1ConstrainedPhase3ResiduesK3 G) :
    D1ConstrainedPhase3Residues3 G :=
  ⟨d1CaseThreeKlingen3_of_residue3 hmod hsp hβ h1s h2 h3 h84 hCGT hD2
      (d1KlingenResidue3_of_other hmod hsp3 hsp5 hK7 hOut h84 h85 h86 h93 hD2 hPar hC3 hAlt hOne
        h.klingen),
    d1ConstrainedWeakBlockResidue3_of_kfacts hK hK5 hK6 hOut h85 h93 hD2⟩

theorem D1ConstrainedPhase3Residues3.toK3 (h : D1ConstrainedPhase3Residues3 G) :
    D1ConstrainedPhase3ResiduesK3 G :=
  ⟨(D1KlingenResidue3.of_klingen3 h.klingen).other⟩

structure D1FrontierResidues3K (G : Type) [Group G] [Finite G] : Prop where
  constrained : D1ConstrainedPhase3ResiduesK3 G
  oneSmall : D1CaseOneSmall3 G
  twoCentral : D1CaseTwoCentral3 G
  twoRest : D1CaseTwoRest3b G

theorem D1FrontierResidues3K.toFrontier (hk : D1CaseThreeFineKFacts3) (hk3 : D1CaseThreeKFacts3)
    (hr : D1CaseThreeReeFacts3) (hc : D1CaseThreeChevFacts3) (hb : KFactBlockPerfectCoreThree)
    (hb5 : KFactBlockSylowThreeAut) (hb6 : KFactBlockHeisenbergAut) (hmod : StmtKlingenModel)
    (hsp : KFactKlingenLocal) (hsp3 : KFactKlingenThreeLocal) (hsp5 : KFactKlingenFiveLocal)
    (hK7 : KFactBlockHeisenbergInner) (hk2 : D1CaseTwoKFacts3 G) (hk2b : D1CaseTwoRest3Facts)
    (hgrp : CaseTwoGroupFacts) (hsyl : KFactKlingenSylowNormalCyclic)
    (h : D1FrontierResidues3K G) :
    D1FrontierResidues3 G :=
  have hfine : D1CaseThreeFineResidues3 G := D1CaseThreeFineResidues3.of_kfacts hk
  have h2 : D1CaseTwo3 G :=
    d1CaseTwo3_of_residues3b hk2 hk2b
      ⟨h.twoCentral, hfine.notKlingen hk3 hr hc, h.constrained.klingen, hsp, hmod, hsyl,
        hgrp⟩
      h.twoRest
  ⟨h.constrained.toResidues3 hb hb5 hb6 hk.outElemRank hk.eightFive hk.nineThree hk.noXBlock hmod
      hsp hsp3 hsp5 hK7 hk.beta hk.eightFour hk.eightSix hk.parabolicThree hk.citedBlockThree
      hk.blockThreeAltSeven hk.blockThreeOneOrbit hk.localCGT h.oneSmall h2
      (hfine.notKlingen hk3 hr hc),
    h.oneSmall, h2, hfine⟩

theorem d1FrontierResidues3K_of_frontier (h : D1FrontierResidues3 G) : D1FrontierResidues3K G :=
  ⟨h.constrained.toK3, h.oneSmall, d1CaseTwoCentral3_of_caseTwo3 h.two,
    d1CaseTwoRest3b_of_rest3 (d1CaseTwoRest3_of_caseTwo3 h.two)⟩

theorem d1FrontierResidues3K_of_theoremD1 (hD1 : TheoremD1 G) : D1FrontierResidues3K G :=
  d1FrontierResidues3K_of_frontier (d1FrontierResidues3_of_theoremD1 hD1)

end CFSG.LocalAnalysis.RankThreeTheoremC
