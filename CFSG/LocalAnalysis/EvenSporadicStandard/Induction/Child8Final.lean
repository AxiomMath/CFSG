module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Child8
import CFSG.Sporadic.Bridge.MonsterModelsGriess
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.SevenFinal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Final
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.LitBridge
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24ModelProved
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzFixedNotLamProved
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzK2FixedNotLam2Proved
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONK2FixedNotLamProved
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzOuterNoLinkProved
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzAutCentralizerN0Proved
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi23InvolutionFixedProved
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1CoverRankProved
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1NotInG2Proved
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HNTwoHS
import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Unconditional2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.FactsAtlasRest
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65UniqFinal
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FiEntries
public import CFSG.LocalAnalysis.EvenSporadicStandard.Children
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SL7Reduce2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SecondLayer3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.Final3
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.MainHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.StdUHered

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard

theorem largeExclusion_of_sol78
    (hUstd : Balance.StdUHered)
    (h7 : ∀ (H : Type) [Group H] [Finite H], Balance.UHered H → Sol78PredS sevenTypes H)
    (hfi : ∀ (H : Type) [Group H] [Finite H], Balance.UHered H → Sol78PredS fiTypes H)
    (hsc : Fi.V3.Fi23SelfCentralizing) (hTh : ThStd.ThSylowWreathPair) : LargeExclusion := by
  intro G _ _ L h
  have hG : Balance.UHered G := hUstd G L h
  have c23 : Nat.card (Carrier .Fi23) = 4089470473293004800 := CFSG.Sporadic.Fi23.card_Fi23
  have hMc : Nat.card (Carrier .M) = CFSG.Open.monsterOrder :=
    (Nat.card_congr CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.toEquiv).trans
      CFSG.Milestones.fam_m_finiteness
  have hMs : IsSimpleGroup (Carrier .M) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.isSimpleGroup_y443Derived
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun h2 => largeExclusion_covers G L h h2⟩
  · exact not_isSporadic_of_sol78PredS (h7 G hG) h (by simp [sevenTypes]) suz_pinned.2.1
      (by rw [suz_pinned.2.2.2, c23]; norm_num)
  · exact not_isSporadic_of_sol78PredS (h7 G hG) h (by simp [sevenTypes]) ru_isSimpleGroup
      (by rw [card_carrier_ru, c23]; norm_num)
  · exact not_isSporadic_of_sol78PredS (h7 G hG) h (by simp [sevenTypes]) on_pinned.2.1
      (by rw [on_pinned.2.2.2, c23]; norm_num)
  · exact not_isSporadic_of_sol78PredS (h7 G hG) h (by simp [sevenTypes]) co1_pinned.2.1
      (by rw [co1_pinned.2.2.2, c23]; norm_num)
  · exact not_isSporadic_of_sol78PredS (hfi G hG) h (by simp [fiTypes]) Fi.fi22_simple
      (by
        rw [show Nat.card (Carrier .Fi22) = 64561751654400 from CFSG.Sporadic.Fi22.card_Fi22, c23]
        norm_num)
  · exact not_isSporadic_fi23_of_sol78PredS (hfi G hG) h (by simp [fiTypes]) Fi.fi23_simple hsc
  · exact not_isSporadic_of_sol78PredS (hfi G hG) h (by simp [fiTypes]) Fi.fi24_simple
      (by
        rw [show Nat.card (Carrier .Fi24Prime) = 1255205709190661721292800 from
          CFSG.Sporadic.Fi24.card_Fi24prime, c23]
        norm_num)
  · exact not_isSporadic_of_sol78PredS (h7 G hG) h (by simp [sevenTypes])
      (show IsSimpleGroup (Carrier .HN) from CFSG.Sporadic.HN.isSimpleGroup_HN)
      (by
        rw [show Nat.card (Carrier .HN) = 273030912000000 from CFSG.Sporadic.HN.card_HN, c23]
        norm_num)
  · exact not_isSporadic_of_sol78PredS (h7 G hG) h (by simp [sevenTypes])
      (show IsSimpleGroup (Carrier .B) from CFSG.Sporadic.B.fam_b_simplicity)
      (by
        rw [show Nat.card (Carrier .B) = CFSG.Open.monsterBabyOrder from
          CFSG.Monster.Existence.card_nativeB, c23]
        norm_num [CFSG.Open.monsterBabyOrder])
  · exact not_isSporadic_of_sol78PredS (h7 G hG) h (by simp [sevenTypes]) hMs
      (by
        rw [hMc, c23]
        norm_num [CFSG.Open.monsterOrder])
  · exact ThStd.th_not_standard_of_secondLayerA
      (ThStd.thSecondLayerA_of_B (ThStd.thSecondLayerB_of_sylowWreathPair hTh))
      ThStd.thLocalData3_th h

theorem largeExclusion_of_inputs
    (lit : CFSG.EvenSporadicStandard.Induction.Sol78LitCore)
    (lx : CFSG.EvenSporadicStandard.Induction.Hyp.Hyp31LitX)
    (hUstd : CFSG.EvenSporadicStandard.Induction.Balance.StdUHered)
    (bFix : CFSG.EvenSporadicStandard.Induction.BFixesElem)
    (babySylow : CFSG.EvenSporadicStandard.Induction.Hyp.BabySylow)
    (babyOvergroups : CFSG.EvenSporadicStandard.Induction.Hyp.BabyOvergroups)
    (e6Fixed : CFSG.EvenSporadicStandard.Induction.Hyp.E6InvolutionFixed)
    (catNoRu : CFSG.EvenSporadicStandard.Induction.Balance.CatalogNoRu)
    (gh1 : CFSG.EvenSporadicStandard.RuStd.S2.GHLemma53_1)
    (thm54 : CFSG.EvenSporadicStandard.Induction.Sol78Thm54ReachHered)
    (onOuterJ1 : CFSG.EvenSporadicStandard.Solomon78.ONOuterFixedJ1)
    (atlas : CFSG.EvenSporadicStandard.Induction.Fi.FiAtlasRest)
    (selfCent : CFSG.EvenSporadicStandard.Induction.Fi.V3.Fi23SelfCentralizing)
    (autSolv : CFSG.EvenSporadicStandard.Induction.Fi.V3.Fi23TranspositionAut)
    (hypOne23 : CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.HypothesisOne
      (CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.Fi23))
    (hypOne24 : CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977.HypothesisOne
      (CFSG.Blueprint.NativeSporadic.Carrier TauCeti.SporadicName.Fi24Prime))
    (lemma63 : CFSG.EvenSporadicStandard.Solomon78.Fi23Lemma63)
    (catFi23Host : CFSG.EvenSporadicStandard.Induction.Balance.CatalogFi23Host)
    (noStdFi22 : CFSG.EvenSporadicStandard.Induction.Fi24NoStdFi22)
    (hTh : ThStd.ThSylowWreathPair)
    (catNoHSOdd : CFSG.EvenSporadicStandard.Induction.Balance.CatalogNoHSOdd)
    (h7 : TwoHSGivesHN) (hChild1 : CentralTwoBound) (hChild10 : TwoFi22Gives)
    (hChild11 : TwoBGivesM) : LargeExclusion :=
  have hR : CoverReductionH := ⟨lit.thm24_1, lit.thm24_3Simple, lx.oddLie, hChild1⟩
  have suzEven : EvenCoverExclHered .Suz :=
    evenCoverExclHered_of_noStd hR (by decide) (by decide)
      fun G _ _ L h hZ => TwoSuz.twoSuz_not_standard_unconditional h hZ
  have ruEven : EvenCoverExclHered .Ru :=
    evenCoverExclHered_of_noStd hR (by decide) (by decide)
      fun G _ _ L h hZ => (largeExclusion_covers G L h hZ).1
  have co1Even : EvenCoverExclHered .Co1 :=
    evenCoverExclHered_of_noStd hR (by decide) (by decide)
      fun G _ _ L h hZ => (largeExclusion_covers G L h hZ).2
  have ev22 : EvenCoverOutHered [.Fi23, .Fi24Prime] .Fi22 :=
    evenCoverOutHered_of_child hR (by decide) (by decide)
      fun G _ _ L h hZ hs => by
        rcases hChild10 G L h hZ hs with h23 | h24
        · exact ⟨.Fi23, by simp, h23⟩
        · exact ⟨.Fi24Prime, by simp, h24⟩
  have evB : EvenCoverOutHered [.M] .B :=
    evenCoverOutHered_of_child hR (by decide) (by decide)
      fun G _ _ L h hZ hs => ⟨.M, by simp, hChild11 G L h hZ hs⟩
  largeExclusion_of_sol78 hUstd
    (fun H _ _ hH => sol78PredS_seven
      lit.toLit lx
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
      bFix evB babySylow babyOvergroups e6Fixed G24Model.g24Model_proved
      co1NotInG2_proved
      (co1CoverRank_proved
        CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
      co1Even (Balance.ruBalanceHered_of_catalog catNoRu) gh1 thm54 ruEven
      catNoHSOdd
      (twoHSHostHered_of_child7 h7 lit.thm24_1 lit.thm24_3Simple lx.oddLie)
      suzFixedNotLam_proved
      suzAutCentralizerN0_proved
      suzOuterNoLink_proved
      suzK2FixedNotLam2_proved suzEven onOuterJ1 onK2FixedNotLam_proved
      H hH)
    (fun H _ _ hH => sol78PredS_fi
      lit.toLit lx
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
      (atlas.toAtlas
        CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds)
      selfCent autSolv fi23InvolutionFixed_proved hypOne23 hypOne24 lemma63
      (Balance.sol78Lemma65KP_of_uniq Balance.sol78Lemma65Uniq_of_certs)
      (Balance.fi23BalanceHered_of_catalog catFi23Host) noStdFi22 ev22 H hH)
    selfCent hTh

end CFSG.EvenSporadicStandard.Induction
