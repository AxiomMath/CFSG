module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.HSMcLLyHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ContainerFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HOvMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43Seven
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterKGA8T
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpRankTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.CatNoOuterHSPump
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIMain
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTC7Harris
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43Config
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTTwoHS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpMcL
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTL4
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTSolomonI
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpTKGA10A8
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSCo1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSKGHSA8Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.PumpHSNoDoubleA8
public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5NoA8Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5NoA8Inner
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5NoA8MinCex
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SecLookupPumpT
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.OuterPumpTSwapStd

public section

namespace CFSG.EvenSporadicStandard.Frontier

open CFSG.Blueprint.NativeSporadic

theorem child6_of_frontier'
    (hHarada39 : HSStd.Harada39One)
    (hHarris311 : HSStd.Harris311)
    (hHarris311HiS : HSStd.Harris311HiS)
    (hKGA6Sq : HSStd.Zassenhaus.PartA.KGA6Sq)
    (hONan77 : HSStd.Zassenhaus.ONan77S5)
    (hONanNoSL29Y : HSStd.Zassenhaus.PartA.ONanNoSL29Y)
    (hCatE16 : HSStd.Zassenhaus.CatE16)
    (hONanInsp : HSStd.Zassenhaus.ONanInspection)
    (hKGHS3 : HSStd.Zassenhaus.KGHS3)
    (hHS38 : CFSG.ComponentClassification.RankTwoSporadic.SporadicCaseOdd .HS)
    (hKGPumpTableT : HSStd.Zassenhaus.Outer.KGPumpTableT)
    (hAltStdFormBigStd : CFSG.OddStandard.AltStdSec.AltStdFormBigStd)
    (hGH312 : TwoHS.GH312Fixed)
    (hHNExcl : HSStd.Zassenhaus.Outer.HNStdExclusionHered)
    (hHighPSL : CFSG.SeitzReduction.SeitzExclusion CFSG.SeitzReduction.HighPSL)
    (hHarada39Two : HSStd.Harada39Two)
    (hLit : Induction.Sol78LitCore)
    (hLx : Induction.Hyp.Hyp31LitX)
    (hSolomon2An : CFSG.ComponentClassification.GSThmB.Solomon2AnInput)
    (hCatDC : Induction.Balance.CatalogNoFixedDoubleCover) :
    HSMcLLyExclusionHered := by
  intro G _ _ hG L h
  have h15 : Induction.FS79Lemma15Hered := hLit.fs79lemma15
  have h13 : Induction.FS79Thm13UseHered := hLit.fs79thm13
  have hMcLLy := Induction.Balance.mcLLyContainerInputs_of_catalog hSolomon2An hCatDC
  have hInner := HSStd.NoA8.hsInnerRest_of_catalog' hHarada39 hHarris311
    hHarris311HiS HSStd.Zassenhaus.PartA.haradaOvergroups_proved
    HSStd.Zassenhaus.PartA.haradaL34Data_proved
    (HSStd.PumpTC7.threeCentralizer7_of_u43 HSStd.U43.threeCentralizer7U43_proved) hKGA6Sq
    hONan77 hONanNoSL29Y HSStd.U43.u43Config_proved HSStd.PumpTC7.harrisL39L43NoD8_proved
    HSStd.U43.u43CoverOrbit_proved hCatE16 hONanInsp h15 hKGHS3 h13 hHS38
  have hX := HSStd.Zassenhaus.Outer.mclStdExclusion_of_container hSolomon2An hMcLLy.containerMcL
  have hSol := HSStd.Zassenhaus.Outer.solomonTwoHSCentralizer_of_gh312 hGH312
  have hGood := HSStd.hsOuterGoodCase_of_pumpT_std hKGPumpTableT h13
    HSStd.PumpT.kgPumpRank_proved HSStd.PumpHS.kgHSA8_proved HSStd.PumpHS.kgHSNoDoubleA8_proved
    HSStd.PumpHS.co1InvCentralizers_proved HSStd.Zassenhaus.Outer.rankTwoStdRec_proved
    hLit.thm24_1 hLx.oddLie hAltStdFormBigStd hSolomon2An centralTwoBound hHNExcl hX hHighPSL
    h15 HSStd.PumpT.l4CentralTwoTrivial_proved hSol
    HSStd.PumpT.solomonIAltCentralizer_proved HSStd.PumpT.kgA10A8_proved
    (HSStd.Zassenhaus.Outer.kgA8Q8_of_T hKGPumpTableT) HSStd.PumpT.kgA8CoverElem_proved
  have hSwap := HSStd.hsOuterSwapFree_of_pumpT_std hKGPumpTableT h13
    HSStd.PumpT.kgPumpRank_proved HSStd.PumpHS.kgHSA8_proved HSStd.PumpHS.kgHSNoDoubleA8_proved
    HSStd.PumpHS.co1InvCentralizers_proved HSStd.Zassenhaus.Outer.rankTwoStdRec_proved
    hLit.thm24_1 hLx.oddLie hAltStdFormBigStd hSolomon2An centralTwoBound hHNExcl hX hHighPSL
    HSStd.PumpT.l4CentralTwoTrivial_proved hSol
    HSStd.PumpT.solomonIAltCentralizer_proved HSStd.PumpT.kgA10A8_proved
  have hL44 := HSStd.hsOuterL44Free_of_pumpT hKGPumpTableT h13
    HSStd.PumpT.kgPumpRank_proved HSStd.Zassenhaus.Outer.rankTwoStdRec_proved
    HSStd.PumpHS.co1InvCentralizers_proved hLit.thm24_1 hLx.oddLie hHighPSL
    HSStd.PumpT.l4CentralTwoTrivial_proved
  have hP13 := HSStd.NoA8.hsMinCexProp13_of_lemma15 h15
  have hHS5 := HSStd.hsSection5_of_steps' hInner hGood hL44 hSwap hHarada39
    HSStd.haradaFourInspection_proved
    (HSStd.NoA8.hsOuterFiveYStep_of_harada39Two HSStd.hs100Model hHarada39Two) hP13
    (HSStd.NoA8.hsMinCexLemma21_of_inputs hP13 hLit.thm24_1 hLx.oddLie)
    (HSStd.catNoOuterHS_of_kgPumpTableT hKGPumpTableT)
  exact ⟨HSStd.hs_not_standard_of_section5At (hHS5 G hG) h,
    (McLStd.mcl_ly_not_standard_of_container hMcLLy h).1,
    (McLStd.mcl_ly_not_standard_of_container hMcLLy h).2⟩

end CFSG.EvenSporadicStandard.Frontier
