module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.LitBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HNTwoHS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpKillType
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Child8
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.RowEntries
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HNOuterProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HSFixNsProved
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MultSporadic
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp

theorem hnStdExclusionHered_of_hnRow
    (lit : Sol78LitCore) (lx : Hyp31LitX) (h7 : TwoHSGivesHN)
    (catNoHSOdd : Balance.CatalogNoHSOdd) :
    HSStd.Zassenhaus.Outer.HNStdExclusionHered := by
  have hSM := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
  have hrow := hn_entry (A := [.HN]) lit.toLit lx (oddMultTrivial_hn_of_sporadicMultipliers hSM)
    { mult_odd := hnMultiplierOdd_of_sporadicMultipliers hSM,
      outer_cent := hnOuterInvCent_proved,
      hs_fix := hsFixedNonsolvable_proved, cat_hs := catNoHSOdd,
      two_hs := twoHSHostHered_of_child7 h7 lit.thm24_1 lit.thm24_3Simple lx.oddLie }
    (by simp)
  have hPred : ∀ (H : Type) [Group H] [Finite H], Balance.UHered H → Sol78PredS [.HN] H :=
    fun H _ _ hH => sol78PredS_of_depRows (rows := [rowEntry [.HN] [] (fun _ => HNPair)])
      (by simp [DepOrdered, rowEntry])
      (fun s hs => ⟨_, List.mem_singleton_self _, by simpa [rowEntry] using hs⟩)
      (fun r hr => by
        rw [List.mem_singleton] at hr
        subst hr
        exact hrow) H hH
  intro G _ _ hG L h
  have c23 : Nat.card (Carrier .Fi23) = 4089470473293004800 := CFSG.Sporadic.Fi23.card_Fi23
  exact not_isSporadic_of_sol78PredS (hPred G hG) h (by simp)
    (show IsSimpleGroup (Carrier .HN) from CFSG.Sporadic.HN.isSimpleGroup_HN)
    (by
      rw [show Nat.card (Carrier .HN) = 273030912000000 from CFSG.Sporadic.HN.card_HN, c23]
      norm_num)

end CFSG.EvenSporadicStandard.Induction
