module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Closed
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Closed
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Closed
public import CFSG.LocalAnalysis.AGLEmbedding.BlockThree

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem d1CaseThreeChevTwoSurvivors_closed (hSchur : KFactChevTwoSurvivorSchur)
    (hKG : KFactG28Local) (hOut : KFactBlockThreeOut) (hSU : KFactBlockNoSU38)
    (hKF : KFactReeF4Local) (hTgtF : StmtReeF4Target) (hElF : KFactJStarElimReeF4)
    (hP5 : KFactBlockFiveParabolic) (hO5 : KFactOutFiveCyclic)
    (hK48 : KFactSp48Local) (hKD48 : KFactSp48Data) (hNine : KFactBlockThreeOrderNine)
    (hTgt48 : StmtSp48Target) (hEl48 : KFactJStarElimSp48) (h48r : D1Sp48NonsolvResidue)
    (hK62 : KFactSp62Local) (hLevi : KFactBlockLeviU42) (h62r : D1Sp62BlockResidue)
    (hβ : KFactBeta) (hP1L : KFactP1ThreeLie) (hP1A : KFactP1ThreeAlt)
    (hP1S : KFactP1ThreeSpor) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hα : KFactThreeOrFiveDvd) (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock) :
    D1CaseThreeSp62 ∧ D1CaseThreeSp48 ∧ D1CaseThreeG28 ∧ D1CaseThreeReeF4 :=
  have hB3 : StmtBlockThree := stmtBlockThree_of h85 h86 h93 hD2 hK2 hC3 hK5
  ⟨d1CaseThreeSp62_closed hSchur hK62 h84 h85 h86 h93 hD2 hB3 stmtBlockInnerNormalizer_of hLevi
      h62r,
    d1CaseThreeSp48_closed hSchur hK48 hKD48 hTgt48 hEl48 hβ hP1L hP1A hP1S h84 h85 h86 h93 hD2
      hB3 stmtBlockInnerNormalizer_of hOut hNine hCGT h48r,
    d1CaseThreeG28_of (stmtG28Data_of (stmtChevTwoSocle_of hSchur) hKG)
      (stmtG28MSide_of h84 h85 h86 h93 hD2 hB3 stmtBlockInnerNormalizer_of hOut hSU),
    d1CaseThreeReeF4_closed hSchur hKF hTgtF hElF hP5 hO5 hβ hP1L hP1A hP1S h84 h85 h86 h93 hB3
      stmtBlockInnerNormalizer_of hα hCGT hD2⟩

end CFSG.AGLEmbedding
