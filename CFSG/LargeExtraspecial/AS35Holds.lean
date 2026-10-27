module

public import CFSG.LargeExtraspecial.AS62C36Main
public import CFSG.LargeExtraspecial.AS35CS64Main
public import CFSG.LargeExtraspecial.AS35FCore
public import CFSG.LargeExtraspecial.AS35GMain
public import CFSG.LargeExtraspecial.AS35JSixFive
public import CFSG.LargeExtraspecial.AS35QFin
public import CFSG.LargeExtraspecial.AS35YUMain
public import CFSG.LargeExtraspecial.AS35ZMMain
public import CFSG.LargeExtraspecial.AS35ZSMain
public import CFSG.LargeExtraspecial.Asc611Final
public import CFSG.LargeExtraspecial.Asc611IMain
public import CFSG.LargeExtraspecial.FS65SixThree
public import CFSG.LargeExtraspecial.S63AAut
public import CFSG.LargeExtraspecial.S63AJ2Cent
public import CFSG.LargeExtraspecial.S63AJ2Schur
public import CFSG.LargeExtraspecial.S63BBender
public import CFSG.LargeExtraspecial.S63CU33
public import CFSG.LargeExtraspecial.S63DSchur

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

theorem aschbacherSmith35Input_holds :
    AschbacherSmith35Input := by
  have hFM : AschbacherSixElevenFusionMStmt :=
    aschbacherSixElevenFusionMStmt_of_inner unitaryInnerCentStmt
  have h512 : AschbacherFiveTwelveCoreStmt :=
    aschbacherFiveTwelveCoreStmt_of_fixFree asc512FixFreeStmt_proof
      suModuleEndInput
  have hRest : AschbacherSecFiveSixRest :=
    aschbacherSecFiveSixRest_of_core' h512 sixFiveTransvectionStmt aschbacherSixSevenMbarStmt
      aschbacherFiveNineOneStmt aschbacherFiveNineTwoStmt aschTwoAutStmt
      (aschbacherSixElevenFusionCoreStmt_of_fusionM hFM)
  have h63g : SmithSixThreeGenInput :=
    smithSixThreeGenInput_of S63.smith55Input S63.autL32Input S63.autA6Input
      S63.smith58Input (S63.smith59Input_of S63.u33CentInput)
      S63.j2CentInput S63.j2SchurInput
  have h63 : SmithSixThreeInput := smithSixThreeInput_of_gen h63g
  exact aschbacherSmith35Input_of_core (aschbacherSmith35Core_of_main
    (aschbacherMainStmt_of_residuals aschbacherWidthTwoResidual_holds aschbacherTwoTwoStmt_of
      aschbacherTIInput hRest)
    (smithSixFiveStmt_of h63 smithSixFourInput))

end CFSG.LargeExtraspecial.S14

