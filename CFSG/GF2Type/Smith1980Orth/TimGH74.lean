module

public import CFSG.CGT.A8S.Final
public import CFSG.CGT.M24S.Main
public import CFSG.GF2Type.Smith1980Orth.Setup
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
public import CFSG.LargeExtraspecial.S111SJMain
public import CFSG.LargeExtraspecial.S11MbFinal
public import CFSG.LargeExtraspecial.S12ModDWMain
public import CFSG.LargeExtraspecial.S12ModUseAsm
public import CFSG.LargeExtraspecial.S14NineA
public import CFSG.LargeExtraspecial.S63AAut
public import CFSG.LargeExtraspecial.S63AJ2Cent
public import CFSG.LargeExtraspecial.S63AJ2Schur
public import CFSG.LargeExtraspecial.S63BBender
public import CFSG.LargeExtraspecial.S63CU33
public import CFSG.LargeExtraspecial.S63DSchur
public import CFSG.LargeExtraspecial.S8A5N
public import CFSG.LargeExtraspecial.S8CBF3D4Main
public import CFSG.LargeExtraspecial.S8KF
public import CFSG.LargeExtraspecial.S8KU
public import CFSG.LargeExtraspecial.S8KX
public import CFSG.LargeExtraspecial.S97RYCert
public import CFSG.LargeExtraspecial.S9RAMain
public import CFSG.LargeExtraspecial.S9RBPMain
public import CFSG.LargeExtraspecial.S9TIPair
public import CFSG.LargeExtraspecial.TI75Bridge
public import CFSG.LargeExtraspecial.TI75Form2
public import CFSG.LargeExtraspecial.TI75Trans
public import CFSG.LargeExtraspecial.S111BMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S14

theorem timInputs_of_widthTwo
    (hW2 : AschbacherWidthTwoResidual) : TimInputs := by
  have hCE : CentralExtInput.{0} := centralExtInput
  have hFM : AschbacherSixElevenFusionMStmt :=
    aschbacherSixElevenFusionMStmt_of_inner unitaryInnerCentStmt
  have h512 : AschbacherFiveTwelveCoreStmt :=
    aschbacherFiveTwelveCoreStmt_of_fixFree asc512FixFreeStmt_proof suModuleEndInput
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
      (aschbacherHypCore_of hW2 aschbacherTwoTwoStmt_of aschbacherTIInput hRest)
  have hT75 : CFSG.CGT.Timmesfeld75.SimpleCaseStmt :=
    TI75Bridge.simpleCaseStmt_of_rest
      ⟨CFSG.CGT.A8S.a8SylowInput, CFSG.CGT.M24S.m24SylowInput⟩
  have hDemp : DW.DempwolffLn2Input := DW.D73.dempwolffLn2Input_of h35
    (CFSG.CGT.Timmesfeld75.nodeStatement_of_simpleCase hT75.list)
  have h215 : CFSG.CGT.Timmesfeld75.Lemma215Stmt := CFSG.CGT.Timmesfeld75.lemma215
  have hDWI : DW.DW2OutInspectionInputN :=
    DW.dw2OutInspectionInputN_of_cert DW.dw2FieldInput s12ExcModuleInputN
  have hFS : FSmith1977cOmegaInput :=
    FS77.fsmith1977cOmegaInput_of h35 (FS77.fSmith1977cW4WeakInput_of_main
      (aschbacherMainStmt_of_residuals hW2 aschbacherTwoTwoStmt_of aschbacherTIInput hRest)
      (smithSixFiveStmt_of h63 smithSixFourInput))
  have hInsp5 : Insp5Input :=
    insp5Input_of_residualN hDWI (inspPSL4_ofN s12PSLModuleInputN) (inspPSp_ofN s12SpModuleInputN)
      (inspPOmega_ofN s12OmegaModuleInputN hFS)
  have hTL : CFSG.CGT.Timmesfeld75.ListWCIdentification :=
    CFSG.CGT.Timmesfeld75.listWCIdentification_of_cert
  have hRes97 : S11.Residual97For111 :=
    S11.residual97For111_of hT75 h215 hTL S11.a9WCPairFact S11.m22WCPairFact
  have hCorB : S8.TimmesfeldCorBInput := CFSG.Timmesfeld.timmesfeldCorBInput
  have hFacts : S8.CorBListFacts := S8.corBListFacts_of S8.corBSectResidual
  have hA5Facts : S8.CorBListA5Facts := S8.corBListA5Facts_of S8.corBA5Residual
  exact
    { hAS := aschbacherSmithWideInput_of_core h35
      hDW := DW.dw37Statement_ofN CFSG.Timmesfeld.arsInput hDWI hDemp
      hRI := rootInvolutionComponentsInput
      hARS := CFSG.Timmesfeld.arsInput
      hTri := S12Tri.fischerTrialityInput
      hFischer := s12FischerStatement
      hInsp := hInsp5
      h36 := timmesfeld36Input_of hFS
      hSL := SL4Mod.s12SL4ModuleInput
      hTI := TI75.weaklyClosedTITransitive_of_inputs hT75 h215
      hF2 := TI75.form2StrongStmt_of_inputs hT75 h215 hTL
      hBen := Bender.benderConjCountInput
      hCE := hCE
      h111 := S11.s11_1Stmt_of_noCommuting
        (S11.noCommuting111_of (S11.a5Input111_of S11.tiClaim111 hRes97))
        (S11.shultInput111_of_NI (S11.shultF6ResidualNI_of S11.shultF6ResidualE_of))
      h118 := fun _ _ _ _ S => S11.timmesfeld11_8M2 S
      hCorB := hCorB
      hFacts := hFacts
      h83 := s8_3Stmt_of S9.tiPairInput S8.timmesfeld83A5InfLinBadE.{0}
        S9.pgl25ConjResidual S9.pgl25TypeIIResidual
        (S8.timmesfeld83PlusGlobal4_of hT75 h215) S8.timmesfeld83PlusGlobal3
        hCorB hFacts hA5Facts hCE
      hRes := S9.timmesfeld93Residual
      h9 := s9a6pglStmt_of hCE }

theorem timInputs_of_gh74
    (hgh : CFSG.LargeExtraspecial.AS35W.GH74Models) : TimInputs :=
  timInputs_of_widthTwo (aschbacherWidthTwoResidual_of_gh74 hgh AS35W.rankTwoW2Input)

end CFSG.GF2Type.Smith1980Orth
