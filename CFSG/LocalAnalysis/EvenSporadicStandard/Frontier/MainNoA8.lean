module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.Child1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.Child2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.Child4
public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.Child5
public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.Child7
public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.Child8
public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.Child10
public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.Child11
public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.Child12
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.NoHSOddPump
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsAtlasParts
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.OddSporadicHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.RuHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.Fi23HostHolds
public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.Child6NoA8
public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.HSMcLLyHeredStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Rbc.Rows

public section

namespace CFSG.EvenSporadicStandard.Frontier

open CFSG.Blueprint.NativeSporadic CFSG.Open

theorem modelsStatement_of_frontier'
    (hFS79 : M12Std.Rbc.RowsToChild3)
    (hCatZ2A6 : CatNoAlmostSimpleZ2 (alternatingGroup (Fin 6)))
    (hA6A6 : M22Std.Prop21A6A6Case)
    (hCatZ2A7 : CatNoAlmostSimpleZ2 (alternatingGroup (Fin 7)))
    (hHypA : M24Std.Ega81HypAZ2A8K)
    (hHarrisSolomon : M24Std.HarrisSolomonZ2S6IsoK)
    (hCatM10 : CatM10AlmostSimple)
    (hS16Loc : Fin76b.Fin76bOuterS16Loc)
    (hS84 : Fin76b.Fin76bOuterS8₄)
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
    (hHighPSL : CFSG.SeitzReduction.SeitzExclusion CFSG.SeitzReduction.HighPSL)
    (hHarada39Two : HSStd.Harada39Two)
    (hLit : Induction.Sol78LitCore)
    (hSolomon2An : CFSG.ComponentClassification.GSThmB.Solomon2AnInput)
    (hCatDC : Induction.Balance.CatalogNoFixedDoubleCover)
    (hHaradaHN : TwoHS.HaradaHNRecognitionKP)
    (hUstd : Induction.Balance.StdUHered)
    (hGH1 : RuStd.S2.GHLemma53_1)
    (hThm54 : Induction.Sol78Thm54ReachHered)
    (hHypOne24 : CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.HypothesisOne
      (Carrier .Fi24Prime))
    (hThWreath : ThStd.ThSylowWreathPair)
    (hChild9 : Co2Exclusion)
    (hFi24 : TwoFi22.DS81.Fi24RecognitionLocal)
    (hGH74 : CFSG.LargeExtraspecial.AS35W.GH74Models)
    (hDS210 : TwoB.DS81Lemma210Two)
    (hFi22Covers : Induction.Fi.Fi22CoversFixesElem)
    (hU62Covers : Induction.Fi.U62CoversFixesElem)
    (hU62Odd : Induction.Fi.U62OddExclHered) :
    ModelsStatement := by
  have hCatNoRu : Induction.Balance.CatalogNoRu :=
    CFSG.ComponentClassification.CatFC.catalogNoRu_holds
  have hCatFi23Host : Induction.Balance.CatalogFi23Host :=
    CFSG.ComponentClassification.CatFC.catalogFi23Host_holds
  have hLx : Induction.Hyp.Hyp31LitX :=
    ⟨CFSG.ComponentClassification.CatFC.oddLieCompNotSporadic_holds⟩
  have hChild1 : CentralTwoBound :=
    child1_of_frontier
  have hChild7 : TwoHSGivesHN :=
    (child7_of_frontier hHaradaHN hGH312)
  have hChild10 : TwoFi22Gives :=
    (child10_of_frontier hFi24)
  have hChild11 : TwoBGivesM :=
    (child11_of_frontier hGH74 hDS210)
  have hCatNoHSOdd : Induction.Balance.CatalogNoHSOdd :=
    (Induction.Balance.catalogNoHSOdd_of_kgPumpTableT hKGPumpTableT)
  have hAtlas : Induction.Fi.FiAtlasRest :=
    (Induction.Fi.FiAtlasRest.of_parts hFi22Covers hU62Covers hU62Odd)
  have hLarge : LargeExclusion :=
    (child8_of_frontier hLit hLx hUstd hCatNoRu hGH1 hThm54 hAtlas hHypOne24
      hCatFi23Host hThWreath hCatNoHSOdd hChild7 hChild1 hChild10 hChild11)
  have hHNExcl : HSStd.Zassenhaus.Outer.HNStdExclusion :=
    (HSStd.Zassenhaus.Outer.hnStdExclusion_of_largeExclusion hLarge)
  have hChild4 : M22M23M24Exclusion :=
    (child4_of_frontier hCatZ2A6 hA6A6 hCatZ2A7 hHypA hHarrisSolomon)
  have hChild5 : J1J3J4Exclusion :=
    (child5_of_frontier hCatZ2A6 hCatM10 hS16Loc hS84 hHypA hHarrisSolomon)
  have hChild6 : HSMcLLyExclusion :=
    (child6_of_frontier' hHarada39 hHarris311 hHarris311HiS hKGA6Sq hONan77 hONanNoSL29Y hCatE16
      hONanInsp hKGHS3 hHS38 hKGPumpTableT hAltStdFormBigStd hGH312 hHNExcl.hered hHighPSL
      hHarada39Two hLit hLx hSolomon2An hCatDC).of_std hUstd
  have hChild12 : J2Exclusion :=
    (child12_of_frontier hCatZ2A6 hCatM10 hS16Loc hS84)
  exact modelsStatement_of_children
    hChild1
    child2_of_frontier
    (hFS79 hChild4 hChild5 hChild6 hChild7 hLarge hChild9 hChild10 hChild11 hChild12)
    hChild4
    hChild5
    hChild6
    hChild7
    hLarge
    hChild9
    hChild10
    hChild11
    hChild12

end CFSG.EvenSporadicStandard.Frontier
