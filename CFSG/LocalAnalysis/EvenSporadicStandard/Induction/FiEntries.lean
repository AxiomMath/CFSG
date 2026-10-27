module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.AtlasFinalV3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Claim612
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Z4
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiSmall
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.TMemFi22Aut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MultSporadicFi

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Fi
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 CFSG.RankThree.PartTwo.Sec4.Census

theorem sol78PredS_fi
    (lit : Sol78Lit) (lx : Hyp.Hyp31LitX) (hSM : SporadicMultipliers)
    (atlas : FiAtlas) (selfCent : V3.Fi23SelfCentralizing)
    (autSolv : V3.Fi23TranspositionAut) (fixed : V3.Fi23InvolutionFixed)
    (hypOne23 : HypothesisOne (Carrier .Fi23))
    (hypOne24 : HypothesisOne (Carrier .Fi24Prime)) (lemma63 : Fi23Lemma63)
    (lemma65 : Balance.Sol78Lemma65KP) (balance23 : Fi23BalanceHered)
    (noStdFi22 : Fi24NoStdFi22) (ev22 : EvenCoverOutHered [.Fi23, .Fi24Prime] .Fi22)
    (H : Type) [Group H] [Finite H] (hH : Balance.UHered H) : Sol78PredS fiTypes H :=
  have h12 : Hyp12Fi := ⟨lit.hyp12Lie, ev22⟩
  have hmult : OddMultTrivial .Fi23 := fun L _ _ hq _ hs =>
    fi23Mult_of_sporadicMultipliers hSM L hq hs
  have claim612E : V3.Fi23Claim612EStarHered :=
    V3.fi23Claim612EStarHered_of_balance hmult balance23
  have pf : FiPinned :=
    fiPinned_of_mult (fi23Mult_of_sporadicMultipliers hSM) (fi24Mult_of_sporadicMultipliers hSM)
      atlas
  have rf : V3.FiV3RowFacts :=
    { thm24 := pinThm24Hex24 lieModelOrders
      transpositions := V3.fi23Transpositions_real
      autSolv := autSolv
      fixed := fixed }
  have coexistMax : V3.FiCoexistMax :=
    V3.fiCoexistMax_of_star fiOrders hmult (fi23FixesElem_of_atlas hmult atlas.fi22Covers)
      (fi24InFixesElem_of_atlas atlas.fi22Covers)
      (Cx.fiHyp31Max_of_atlas pf h12 lieModelOrders atlas lx) lemma63 lemma65
      lit.lemma25 hypOne23 h12 balance23 claim612E
  have hI : FiInputs :=
    { lemma25 := lit.lemma25
      rank22 := (fi22_atlasFacts (fi22FixesElem_of_atlas atlas.u62Covers)).pRank_L
      rank23 := (fi23_atlasFacts hmult (fi23FixesElem_of_atlas hmult atlas.fi22Covers)).pRank_L
      rank24 := (fi24_atlasFacts (fi24InFixesElem_of_atlas atlas.fi22Covers)).pRank_L
      hypOne23 := hypOne23
      hypOne24 := hypOne24
      mult23 := hmult
      lemma63 := lemma63
      lemma65 := lemma65
      balance23 := balance23
      claim612E := V3.fi23Claim612E_of_star claim612E
      tail23 := fun H _ _ hH N L K t u hN hidx hkp hcov hglob hfi hS htN =>
        V3.fi23TailMax_of_hyp12 h12
          (fun L _ _ hq _ hs => fi23Mult_of_sporadicMultipliers hSM L hq hs) H hH N L K t u hN
          hidx hkp hcov hglob (fiInBase_iff.1 hfi).1 hS htN
      cfg610 := fi24Cfg610Hyp35_of_comp (fi24InFixesElem_of_atlas atlas.fi22Covers)
        (fi24Cfg610Comp_of_hyp12
          (Cx.fi24Cfg610Hyp12_of_engine pf h12 lieModelOrders atlas))
      noStdFi22 := noStdFi22 }
  holds_of_stepSec
    (step_fi (fiStage3_of_main fiSmallFStar
      (fiStage3Main_of_literatureV3
        { mult23 := fi23Mult_of_sporadicMultipliers hSM
          mult24 := fi24Mult_of_sporadicMultipliers hSM
          atlas := atlas
          hyp12 := h12
          lx := lx
          tmem22 := tMemOfNotMax_fi22_final
          selfCent := selfCent
          autSolv := autSolv
          fixed := fixed
          coexistMax := coexistMax
          outerInv := V3.fiOuterInvolution_of_engine pf h12 lieModelOrders atlas rf
            lx.oddLie (fi24InFixesElem_of_atlas atlas.fi22Covers) })) lit hI.closing
      hI.given) H hH

end CFSG.EvenSporadicStandard.Induction
