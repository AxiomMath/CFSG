module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.Milestone
public import CFSG.LocalAnalysis.EvenSporadicStandard.Frontier.MainNoA8

public section

namespace CFSG.EvenSporadicStandard.Frontier

open CFSG.Blueprint.NativeSporadic CFSG.Open CFSG.Milestones


theorem ctss_models_of_frontier'
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
    ModelsStatement :=
  modelsStatement_of_frontier'
    hFS79 hCatZ2A6 hA6A6 hCatZ2A7 hHypA hHarrisSolomon hCatM10 hS16Loc hS84 hHarada39 hHarris311
    hHarris311HiS hKGA6Sq hONan77 hONanNoSL29Y hCatE16 hONanInsp hKGHS3 hHS38 hKGPumpTableT
    hAltStdFormBigStd hGH312 hHighPSL hHarada39Two hLit hSolomon2An hCatDC hHaradaHN hUstd
    hGH1 hThm54 hHypOne24 hThWreath hChild9 hFi24 hGH74 hDS210
    hFi22Covers hU62Covers hU62Odd

theorem ctss_order_of_frontier'
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
    OrderStatement := by
  intro G _ _ _ hnonab hK L hL hcore S hS htype hexc hres hspor hMJ
  have hMc : Nat.card (Carrier .M) = monsterOrder :=
    (Nat.card_congr CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.toEquiv).trans
      CFSG.Milestones.fam_m_finiteness
  rcases modelsStatement_of_frontier'
      hFS79 hCatZ2A6 hA6A6 hCatZ2A7 hHypA hHarrisSolomon hCatM10 hS16Loc hS84 hHarada39 hHarris311
      hHarris311HiS hKGA6Sq hONan77 hONanNoSL29Y hCatE16 hONanInsp hKGHS3 hHS38 hKGPumpTableT
      hAltStdFormBigStd hGH312 hHighPSL hHarada39Two hLit hSolomon2An hCatDC hHaradaHN hUstd
      hGH1 hThm54 hHypOne24 hThWreath hChild9 hFi24 hGH74 hDS210
      hFi22Covers hU62Covers hU62Odd
      G hnonab hK L hL hcore S hS htype hexc hres hspor hMJ with
    ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · rw [(Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Co3.card_Co3,
      standardComponentEvenSporadicOrders]
    norm_num
  · rw [(Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HN.card_HN,
      standardComponentEvenSporadicOrders]
    norm_num
  · rw [(Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Fi22.card_Fi22,
      standardComponentEvenSporadicOrders]
    norm_num
  · rw [(Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Fi23.card_Fi23,
      standardComponentEvenSporadicOrders]
    norm_num
  · rw [(Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Fi24.card_Fi24prime,
      standardComponentEvenSporadicOrders]
    norm_num
  · rw [(Nat.card_congr e.toEquiv).trans CFSG.Monster.Existence.card_nativeB,
      standardComponentEvenSporadicOrders, monsterBabyOrder]
    norm_num
  · rw [(Nat.card_congr e.toEquiv).trans hMc, standardComponentEvenSporadicOrders, monsterOrder]
    norm_num

end CFSG.EvenSporadicStandard.Frontier
