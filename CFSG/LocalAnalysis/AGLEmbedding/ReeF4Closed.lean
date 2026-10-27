module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeReeF4
public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4MSide
public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Data
public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Components

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem stmtReeF4Components_of (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hB3 : StmtBlockThree)
    (hb : StmtBlockInnerNormalizer) (hα : KFactThreeOrFiveDvd) (hP5 : KFactBlockFiveParabolic)
    (hO5 : KFactOutFiveCyclic) : StmtReeF4Components :=
  fun h hind _ _ hLb => h.le_centralizer_component hind h84 h85 h86 h93 hD2 hB3 hb hα hP5 hO5
    stmtComponentRank stmtBarPRankLift hLb

theorem d1CaseThreeReeF4_closed (hSchur : KFactChevTwoSurvivorSchur) (hKF : KFactReeF4Local)
    (hTgt : StmtReeF4Target) (hEl : KFactJStarElimReeF4) (hP5 : KFactBlockFiveParabolic)
    (hO5 : KFactOutFiveCyclic) (hβ : KFactBeta) (hP1L : KFactP1ThreeLie)
    (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor) (h84 : Asc81bEightFour)
    (h85 : Asc81bEightFive) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hB3 : StmtBlockThree) (hb : StmtBlockInnerNormalizer) (hα : KFactThreeOrFiveDvd)
    (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) : D1CaseThreeReeF4 :=
  d1CaseThreeReeF4_of (stmtChevTwoSocle_of hSchur) (stmtReeF4Data_of hKF)
    (stmtReeF4MSide_of h84 hD2 (stmtReeF4Components_of h84 h85 h86 h93 hD2 hB3 hb hα hP5 hO5))
    hTgt hEl hβ hP1L hP1A hP1S h84 hCGT hD2

end CFSG.AGLEmbedding
