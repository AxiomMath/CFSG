module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpTableHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.NoFixedDoubleCoverHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentralizerFacts
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.DS81EvenHolds
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Final
public import CFSG.LocalAnalysis.OddStandard.AltStdFormBigStd
import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.GH312.AlmostSimple
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveRhoMain
import CFSG.LocalAnalysis.SeitzReduction.SeitzFamiliesFinalElevenGLS3
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.CatNoOuterHSPump
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HOvMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.OuterPumpTSwapStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSCo1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSKGHSA8Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSNoDoubleA8
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Harris
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTKGA10A8
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTL4
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTSolomonI
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5NoA8Inner
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5NoA8Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5NoA8MinCex
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SecLookupPumpT
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43Config
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43Seven
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterKGA8T
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpMcL
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTTwoHS
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ContainerFinal

public section

namespace CFSG.EvenSporadicStandard.Frontier

open CFSG.Blueprint.NativeSporadic CFSG.Yardstones.M1442643da6f2

theorem hsSection5Hered_of_ctssInputs
    (h05 : InvolutionCentralizerTheorems) (h06 : ONanInputs)
    (hL15 : Induction.FS79Lemma15Hered) (hThm13 : Induction.FS79Thm13UseHered)
    (hCIT : Induction.CITPart2)
    (hHNExcl : HSStd.Zassenhaus.Outer.HNStdExclusionHered) : HSStd.HSSection5Hered := by
  have hThm241 : Induction.Sol78Thm24_1Use := Induction.sol78Thm24_1Use_of_citPart2 hCIT
  have hHighPSL := CFSG.SeitzReduction.seitzExclusion_highPSL_of_final11_gls3
    CFSG.SeitzReduction.LinearPilot.lFiveFieldTildeSplitInput_holds
  have hKGPumpTableT := CFSG.ComponentClassification.CatFC.kgPumpTableT_holds
  have hCatDC := CFSG.ComponentClassification.CatFC.catalogNoFixedDoubleCover_holds
  have h07 := CFSG.ComponentClassification.CatFC.catalogueCentralizerFacts_of_ds81Even
    CFSG.ComponentClassification.CatFC.DS81.ds81EvenLie_holds
  have hStd := CFSG.OddStandard.AltStdSec.altStdFormBigStd_holds
  have hSolomon2An := CFSG.OddStandard.Solomon75.solomon2AnInput_of_gh74Milestone
    @CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models
  have hHS38 := CFSG.ComponentClassification.RankTwoSporadic.HS.sporadicCaseOdd_HS
    CFSG.ComponentClassification.RankTwoFoundation.lemma32
    CFSG.ComponentClassification.RankTwoFoundation.lemma33Three
  have hlie := CFSG.ComponentClassification.CatFC.oddLieCompNotSporadic_holds
  have hMcLLy := Induction.Balance.mcLLyContainerInputs_of_catalog hSolomon2An hCatDC
  have hInner := HSStd.NoA8.hsInnerRest_of_catalog' h05.harada39One h05.harris311
    h05.harris311HiS HSStd.Zassenhaus.PartA.haradaOvergroups_proved
    HSStd.Zassenhaus.PartA.haradaL34Data_proved
    (HSStd.PumpTC7.threeCentralizer7_of_u43 HSStd.U43.threeCentralizer7U43_proved) h07.kgA6Sq
    h06.onan77S5 h06.onanNoSL29Y HSStd.U43.u43Config_proved HSStd.PumpTC7.harrisL39L43NoD8_proved
    HSStd.U43.u43CoverOrbit_proved h07.catE16 h06.onanInspection hL15 h07.kgHS3
    hThm13 hHS38
  have hX := HSStd.Zassenhaus.Outer.mclStdExclusion_of_container hSolomon2An hMcLLy.containerMcL
  have hSol := HSStd.Zassenhaus.Outer.solomonTwoHSCentralizer_of_gh312
    (TwoHS.GH312.gh312Fixed_of_gh74 fun G _ _ _ hnonab hrank hsect =>
      CFSG.Milestones.cl_lit_gh74_sectional_two_rank_four_models G hnonab hrank hsect)
  have hGood := HSStd.hsOuterGoodCase_of_pumpT_std hKGPumpTableT hThm13
    HSStd.PumpT.kgPumpRank_proved HSStd.PumpHS.kgHSA8_proved HSStd.PumpHS.kgHSNoDoubleA8_proved
    HSStd.PumpHS.co1InvCentralizers_proved HSStd.Zassenhaus.Outer.rankTwoStdRec_proved
    hThm241 hlie hStd hSolomon2An centralTwoBound hHNExcl hX hHighPSL
    hL15 HSStd.PumpT.l4CentralTwoTrivial_proved hSol
    HSStd.PumpT.solomonIAltCentralizer_proved HSStd.PumpT.kgA10A8_proved
    (HSStd.Zassenhaus.Outer.kgA8Q8_of_T hKGPumpTableT) HSStd.PumpT.kgA8CoverElem_proved
  have hSwap := HSStd.hsOuterSwapFree_of_pumpT_std hKGPumpTableT hThm13
    HSStd.PumpT.kgPumpRank_proved HSStd.PumpHS.kgHSA8_proved HSStd.PumpHS.kgHSNoDoubleA8_proved
    HSStd.PumpHS.co1InvCentralizers_proved HSStd.Zassenhaus.Outer.rankTwoStdRec_proved
    hThm241 hlie hStd hSolomon2An centralTwoBound hHNExcl hX hHighPSL
    HSStd.PumpT.l4CentralTwoTrivial_proved hSol
    HSStd.PumpT.solomonIAltCentralizer_proved HSStd.PumpT.kgA10A8_proved
  have hL44 := HSStd.hsOuterL44Free_of_pumpT hKGPumpTableT hThm13
    HSStd.PumpT.kgPumpRank_proved HSStd.Zassenhaus.Outer.rankTwoStdRec_proved
    HSStd.PumpHS.co1InvCentralizers_proved hThm241 hlie hHighPSL
    HSStd.PumpT.l4CentralTwoTrivial_proved
  have hP13 := HSStd.NoA8.hsMinCexProp13_of_lemma15 hL15
  exact HSStd.hsSection5_of_steps' hInner hGood hL44 hSwap h05.harada39One
    HSStd.haradaFourInspection_proved
    (HSStd.NoA8.hsOuterFiveYStep_of_harada39Two HSStd.hs100Model h05.harada39Two) hP13
    (HSStd.NoA8.hsMinCexLemma21_of_inputs hP13 hThm241 hlie)
    (HSStd.catNoOuterHS_of_kgPumpTableT hKGPumpTableT)

end CFSG.EvenSporadicStandard.Frontier
