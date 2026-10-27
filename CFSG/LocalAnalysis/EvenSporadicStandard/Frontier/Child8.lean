module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Child8Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24CSelfCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24CTransAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24CNoStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BabyP1Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BabyP3Fix
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BabyP2Over
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.ONOuterJ1Proved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23L63Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.E6FixP4Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi23

public section

namespace CFSG.EvenSporadicStandard.Frontier

open CFSG.Blueprint.NativeSporadic

theorem child8_of_frontier
    (hLit : Induction.Sol78LitCore)
    (hLx : Induction.Hyp.Hyp31LitX)
    (hUstd : Induction.Balance.StdUHered)
    (hCatNoRu : Induction.Balance.CatalogNoRu)
    (hGH1 : RuStd.S2.GHLemma53_1)
    (hThm54 : Induction.Sol78Thm54ReachHered)
    (hAtlas : Induction.Fi.FiAtlasRest)
    (hHypOne24 : CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.HypothesisOne
      (Carrier .Fi24Prime))
    (hCatFi23Host : Induction.Balance.CatalogFi23Host)
    (hThWreath : ThStd.ThSylowWreathPair)
    (hCatNoHSOdd : Induction.Balance.CatalogNoHSOdd)
    (hChild7 : TwoHSGivesHN)
    (hChild1 : CentralTwoBound)
    (hChild10 : TwoFi22Gives)
    (hChild11 : TwoBGivesM) :
    LargeExclusion :=
  Induction.largeExclusion_of_inputs
    hLit hLx hUstd (Induction.bFixesElem_of_oddMultTrivial
        (Induction.oddMultTrivial_b_of_sporadicMultipliers
            CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)) (Induction.Hyp.babySylow_proved)
    (Induction.Hyp.babyOvergroups_proved) (Induction.Hyp.e6InvolutionFixed_proved)
    hCatNoRu hGH1 hThm54 (Solomon78.onOuterFixedJ1_proved) hAtlas
    (Induction.Fi.V3.fi23SelfCentralizing_of_mult (Induction.fi23Mult_of_sporadicMultipliers
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds))
    (Induction.Fi.V3.fi23TranspositionAut_proved) (HypOne.Fi23.hypothesisOne_fi23) hHypOne24
    (Solomon78.fi23Lemma63_proved) hCatFi23Host (Induction.fi24NoStdFi22_proved) hThWreath
    hCatNoHSOdd hChild7 hChild1 hChild10 hChild11

end CFSG.EvenSporadicStandard.Frontier
