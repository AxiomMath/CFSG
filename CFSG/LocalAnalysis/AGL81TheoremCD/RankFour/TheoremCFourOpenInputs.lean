module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ChainCaseOne
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FFGlaubermanNiles
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K7145Holds
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSevenOneOneHolds
public import CFSG.CGT.PushingUpLit.TwoKHolds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FiveFourteenA11UseHolds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FiveTwentyFiveS11UseHolds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34NotInvolvedA11
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A11GammaTwoSet
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K1410aHolds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K4143NoExtraHolds
import CFSG.HardMathSupport.Foote.Coordinator.Downstream
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThree
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K1Holds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThreeOfInputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFactNineFourRankOneAutProof
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFactNineFourStronglyEmbeddedProof
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineSixMoreoverProof
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTwelveOneSigmaStrong
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThreeKFactProof
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineSixInputOfMoreover
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ThreeFiveA11InputHolds
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNormalComplementHolds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenThree
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.K35CentralHolds
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenFive
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.CaseOneFourteenFourOne
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFactNineFourAutMProof
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGL81TheoremCD.RankFour.WitnessFour
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.RankFour

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.LocalAnalysis.AGL81TheoremCD.Section14
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)


theorem o991Gen_of_kFactThreeFiveCentral
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen)
    (hK35c : CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFactThreeFiveCentral) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.O991Gen :=
  CFSG.LocalAnalysis.RankThreeUC.AGL81C.o991Gen_of_inputs h97
    (Section14.nineSixInputGen_of_nineSixMoreoverGen
      (Section14.nineSixMoreoverGen_of_kFactThreeFiveCentral hK35c))
    Section14.threeFiveA11InputGen_holds CFSG.LocalAnalysis.RankThreeUC.AGL81C.zkFacts_holds

theorem fourteenFiveCaseOneGen_of_inputs
    (h1210 : TwelveTenThree) (h1211 : TwelveElevenGen)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen) :
    FourteenFiveCaseOneGen :=
  have hK35c := Section14.K35Central.kFactThreeFiveCentral_holds
  have h96 := Section14.nineSixMoreoverGen_of_kFactThreeFiveCentral hK35c
  have h991 := o991Gen_of_kFactThreeFiveCentral h97 hK35c
  have h142 := Section14.fourteenTwoCaseOneGen_of h1210 h1211 h97 h96 h991
  Section14.fourteenFiveCaseOneGen_of h142 h1210 h1211 h97 h96 h991
    Section14.nineFourTwoSigmaGen_holds
    (Section14.nineTwelveOneSigmaStrong_holds
      CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds)
    (Section14.fourteenFourOneCaseOneGen_of h142 h1211 h991)
    Section14.kFactNineFourAutM_holds

theorem agl81TheoremCFour_of_open_inputs
    (hD : CFSG.Yardstones.Mf4cdcdf2e013.AGL81TheoremDFour)
    (h1210 : TwelveTenThree) (h1211 : TwelveElevenGen)
    (h97 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSevenTwoInputGen) :
    CFSG.Yardstones.Mf4cdcdf2e013.AGL81TheoremCFour :=
  have hK35c := Section14.K35Central.kFactThreeFiveCentral_holds
  have h991 := o991Gen_of_kFactThreeFiveCentral h97 hK35c
  agl81TheoremCFour_of_caseOneInputs hD h1210 h1211 h97
    (Section14.nineSixMoreoverGen_of_kFactThreeFiveCentral hK35c)
    CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds h991
    kFactL34NotInvolvedA11_holds
    (Section14.fourteenTwoCaseOneGen_of h1210 h1211 h97
      (Section14.nineSixMoreoverGen_of_kFactThreeFiveCentral hK35c) h991)
    (Section14.fourteenThreeCaseOneGen_of h1210 h1211 h97
      (Section14.nineSixMoreoverGen_of_kFactThreeFiveCentral hK35c) h991
      CFSG.LocalAnalysis.RankThreeUC.AGL81C.sevenOneOne_holds)
    (fourteenFiveCaseOneGen_of_inputs h1210 h1211 h97)
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.ffModuleTheorem_holds
    CFSG.LocalAnalysis.RankThreeUC.S15.K7145_holds kFact1410a_holds
    k4143NoExtraspecial_holds
    kFactA11GammaTwoSet_holds fiveFourteenA11Use_holds fiveTwentyFiveS11Use_holds
    (sevenThreeInput_of_inputs
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k34odd_holds
      CFSG.LocalAnalysis.RankThreeUC.AGL81C.sevenOneOne_holds
      Section14.kFactA9NotInvolvedK34Classical_holds)
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.sevenOneOne_holds
    (fun G _ _ hC =>
      noXBlockFor_of_inputsK
        CFSG.HardMathSupport.Foote.Coordinator.aschbacherTheoremOneK_proved
        CFSG.CGT.PushingUpLit.aschbacherTheoremTwoK_holds
        CFSG.CGT.PushingUpLit.solomonAlternatingBlockK_holds hC.toStandingGen)
    (fun G _ _ _ M _ _ => fourteenFiveThreeAt_of_inputs nineFourTwoSigmaGen_holds
      (nineTwelveOneSigmaStrong_holds CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds)
      kFactNineFourRankOneAut_holds kFactNineFourStronglyEmbedded_holds M)

end CFSG.LocalAnalysis.AGL81TheoremCD.RankFour
