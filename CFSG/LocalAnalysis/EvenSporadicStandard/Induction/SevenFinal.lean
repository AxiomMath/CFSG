module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.SevenRows
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.RowEntriesRuModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.RowEntriesSO
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.RowEntriesCo1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.E6FourProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.E6CoverRankProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BCoverRankProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BabyCoverProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuBorelProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MFixProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BInvCentProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuFamilyProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HNOuterProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HSFixNsProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1PinnedProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24FixedNonsolvableProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1AutCentralizerA4Proved

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp
  CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 CFSG.Sporadic.SuzOddCore
  CFSG.Sporadic.Co1Block CFSG.RankThree.PartTwo.Sec4.Census

theorem sol78PredS_seven
    (lit : Sol78Lit) (lx : Hyp31LitX) (hSM : SporadicMultipliers)
    (bFix : BFixesElem) (evB : EvenCoverOutHered [.M] .B)
    (babySylow : BabySylow) (babyOvergroups : BabyOvergroups)
    (e6Fixed : E6InvolutionFixed)
    (g24Model : LieModel ↥twoBD .G2 0 2 2)
    (co1NotInG2 : Co1NotInG2) (co1Rank : Co1CoverRank) (co1Even : EvenCoverExclHered .Co1)
    (ruBalance : RuBalanceHered) (gh1 : RuStd.S2.GHLemma53_1)
    (thm54 : Sol78Thm54ReachHered) (ruEven : EvenCoverExclHered .Ru)
    (hnCatNoHSOdd : Balance.CatalogNoHSOdd) (hnTwoHS : TwoHSHostHered)
    (suzFixedNotLam : SuzFixedNotLam) (suzAutN0 : SuzAutCentralizerN0)
    (suzOuter : SuzOuterNoLink) (suzK2Fixed : SuzK2FixedNotLam2) (suzEven : EvenCoverExclHered .Suz)
    (onOuterJ1 : ONOuterFixedJ1) (onK2Fixed : ONK2FixedNotLam)
    (H : Type) [Group H] [Finite H] (hH : Balance.UHered H) : Sol78PredS sevenTypes H :=
  sol78PredS_seven_of_entries (fun _ => ONQ) (fun _ => SuzQ) (fun _ => MPair) (fun _ => BPair)
    (fun _ => PairClass.withGlobals Co1Pair) (fun _ => HNPair) (fun _ => (RuPair).withGlobals)
    (on_entry_row lit lx (OddMultThree.on_of_multThree (onMultThree_of_sporadicMultipliers hSM))
      { outer_j1 := onOuterJ1, k2_fixed := onK2Fixed }
      (by simp [sevenTypes]) (by simp [sevenTypes]))
    (suz_entry_row lit lx suzFixedNotLam
      { aut_centralizer := suzAutN0, outer := suzOuter, k2_fixed := suzK2Fixed, even := suzEven }
      (by simp [sevenTypes]) (by simp [sevenTypes]))
    (m_entry lit lx
      (mFixesElem_proved (Hyp.oddMultTrivial_m (monsterNoCover_of_sporadicMultipliers hSM)))
      { noCover := monsterNoCover_of_sporadicMultipliers hSM,
        bRank := bCoverRank_of_sporadicMultipliers hSM, bInvCent := bInvCent_proved,
        evenB := evB }
      (by simp [sevenTypes]) (by simp [sevenTypes]))
    (b_entry lit lx bFix
      { cover := babyCoverFacts_of_sylow_overgroups babySylow babyOvergroups,
        mult := oddMultTrivial_b_of_sporadicMultipliers hSM,
        quotient := babyQuotient_proved, bRank := bCoverRank_of_sporadicMultipliers hSM,
        e6Rank := e6CoverRank_proved, e6Fixed := e6Fixed, e6Four := e6FourNoEvenCover_proved,
        noCover := monsterNoCover_of_sporadicMultipliers hSM, evenB := evB }
      (by simp [sevenTypes]) (by simp [sevenTypes]))
    (co1_entry_of_tmem lit lx (oddMultTrivial_co1_of_sporadicMultipliers hSM)
      co1PinnedPair_proved
      (co1AutCentralizerA4_proved (oddMultTrivial_co1_of_sporadicMultipliers hSM))
      g24FixedNonsolvable_proved
      { g24_model := g24Model,
        aut_centralizer :=
          co1AutCentralizerN0_proved (oddMultTrivial_co1_of_sporadicMultipliers hSM),
        g24_fixed := g24FixedNonsolvable_proved,
        no_co1 := co1NotInG2, rank := co1Rank, even := co1Even }
      (by simp [sevenTypes]))
    (hn_entry lit lx (oddMultTrivial_hn_of_sporadicMultipliers hSM)
      { mult_odd := hnMultiplierOdd_of_sporadicMultipliers hSM,
        outer_cent := hnOuterInvCent_proved,
        hs_fix := hsFixedNonsolvable_proved, cat_hs := hnCatNoHSOdd, two_hs := hnTwoHS }
      (by simp [sevenTypes]))
    (ru_entry_model lit lx ruLocalFacts_proved
      (oddMultTrivial_ru_of_sporadicMultipliers hSM) ruBalance gh1
      { thm54 := thm54, suzuki := ruSuzukiModel_proved, family := ruFamilyFacts_proved,
        normalizer := ruNormalizerFacts_proved, szCover := szCoverFacts_proved, even := ruEven }
      (by simp [sevenTypes])) H hH

end CFSG.EvenSporadicStandard.Induction
