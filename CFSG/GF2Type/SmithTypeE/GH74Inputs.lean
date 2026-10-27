module

import CFSG.Holt.H78.Bridge
public import CFSG.CGT.A8S.Final
public import CFSG.CGT.M24S.Main
public import CFSG.LargeExtraspecial.AS35CS64Main
public import CFSG.LargeExtraspecial.AS35FCore
public import CFSG.LargeExtraspecial.AS35GMain
public import CFSG.LargeExtraspecial.AS35IMain
public import CFSG.LargeExtraspecial.AS35JSixFive
public import CFSG.LargeExtraspecial.AS35QFin
public import CFSG.LargeExtraspecial.AS35WFinal
public import CFSG.LargeExtraspecial.AS35WRMain
public import CFSG.LargeExtraspecial.AS35YUMain
public import CFSG.LargeExtraspecial.AS35ZMMain
public import CFSG.LargeExtraspecial.AS35ZSMain
public import CFSG.LargeExtraspecial.Asc611Final
public import CFSG.LargeExtraspecial.Asc611IMain
public import CFSG.LargeExtraspecial.D73Main
public import CFSG.LargeExtraspecial.FS65SixThree
public import CFSG.LargeExtraspecial.S12ModDWMain
public import CFSG.LargeExtraspecial.S12ModUseAsm
public import CFSG.LargeExtraspecial.S14SMKTransMain
public import CFSG.LargeExtraspecial.S63AAut
public import CFSG.LargeExtraspecial.S63AJ2Cent
public import CFSG.LargeExtraspecial.S63AJ2Schur
public import CFSG.LargeExtraspecial.S63BBender
public import CFSG.LargeExtraspecial.S63CU33
public import CFSG.LargeExtraspecial.S63DSchur
public import CFSG.LargeExtraspecial.TI75Bridge
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE

open CFSG CFSG.Blueprint CFSG.Open
open Subgroup CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S14

theorem smithTypeEInputs_of_gh74 (hgh : CFSG.LargeExtraspecial.AS35W.GH74Models) :
    AschbacherSmithWideInput ∧ DW.DW37Statement ∧
      CFSG.RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple ∧ S14.SMK.Inputs10 := by
  have hW2 : AschbacherWidthTwoResidual := aschbacherWidthTwoResidual_of_gh74 hgh
    AS35W.rankTwoW2Input
  have hHolt : CFSG.RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple :=
    CFSG.Holt.H78.holtUniqueFixedPointSimple_of_holtTheorem1 CFSG.Holt.H78.holtTheorem1
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
  have h35 : AschbacherThreeTranspositionCore :=
    aschbacherThreeTranspositionCore_of_residuals h63 smithSixFourInput
      (aschbacherHypCore_of hW2 aschbacherTwoTwoStmt_of aschbacherTIInput
        hRest)
  have hT75 : CFSG.CGT.Timmesfeld75.SimpleCaseStmt :=
    TI75Bridge.simpleCaseStmt_of_rest
      ⟨CFSG.CGT.A8S.a8SylowInput, CFSG.CGT.M24S.m24SylowInput⟩
  have hDemp : DW.DempwolffLn2Input := DW.D73.dempwolffLn2Input_of h35
    (CFSG.CGT.Timmesfeld75.nodeStatement_of_simpleCase hT75.list)
  have hDWI : DW.DW2OutInspectionInputN :=
    DW.dw2OutInspectionInputN_of_cert DW.dw2FieldInput s12ExcModuleInputN
  have hFS : FSmith1977cOmegaInput :=
    FS77.fsmith1977cOmegaInput_of h35 (FS77.fSmith1977cW4WeakInput_of_main
      (aschbacherMainStmt_of_residuals hW2 aschbacherTwoTwoStmt_of aschbacherTIInput
        hRest)
      (smithSixFiveStmt_of h63 smithSixFourInput))
  have hInsp5 : Insp5Input :=
    insp5Input_of_residualN hDWI (inspPSL4_ofN s12PSLModuleInputN) (inspPSp_ofN s12SpModuleInputN)
      (inspPOmega_ofN s12OmegaModuleInputN hFS)
  have hdw37 : DW.DW37Statement := DW.dw37Statement_ofN CFSG.Timmesfeld.arsInput hDWI hDemp
  have hModel : SmithEModel :=
    smithEModel_of_inputs rootInvolutionComponentsInput CFSG.Timmesfeld.arsInput
      S12Tri.fischerTrialityInput s12FischerStatement hInsp5 (timmesfeld36Input_of hFS)
      SL4Mod.s12SL4ModuleInput hdw37 (aschbacherSmithWideInput_of_core h35)
  exact ⟨aschbacherSmithWideInput_of_core h35, hdw37, hHolt,
    ⟨rootInvolutionComponentsInput, CFSG.Timmesfeld.arsInput, S12Tri.fischerTrialityInput,
      s12FischerStatement, hInsp5, timmesfeld36Input_of hFS, SL4Mod.s12SL4ModuleInput, hdw37⟩⟩

end CFSG.GF2Type.SmithTypeE
