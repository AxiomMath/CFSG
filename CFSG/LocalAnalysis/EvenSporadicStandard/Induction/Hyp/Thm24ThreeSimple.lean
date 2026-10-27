module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Thm24ThreeSimpleCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpRankTwo
import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.Co0ClsK
import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelOrders
import CFSG.LocalAnalysis.SeitzReduction.RankOneHallTwoArithAltSporSporadic

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

private theorem card_of_isSporadic_of_ne {s : TauCeti.SporadicName} (hTh : s ≠ .Th)
    (hM : s ≠ .M) {Y : Type} [Group Y] (h : IsSporadic Y s) :
    Nat.card Y = CFSG.EvenSmallLie.Child3.sporadicCard s := by
  obtain ⟨e⟩ := h
  exact (Nat.card_congr e.toEquiv).trans (CFSG.EvenSmallLie.Child3.card_carrier s hTh hM)

theorem thm24ThreeSimpleInputs_proved : Thm24ThreeSimpleInputs where
  rankTwo := CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer.rankTwoStdRec_proved
  card_J2 := fun _ _ h => card_of_isSporadic_of_ne (by decide) (by decide) h
  card_He := fun _ _ h => card_of_isSporadic_of_ne (by decide) (by decide) h
  card_Ru := fun _ _ h => card_of_isSporadic_of_ne (by decide) (by decide) h
  card_Suz := fun _ _ h => card_of_isSporadic_of_ne (by decide) (by decide) h
  co1 := fun _ _ h _ hu =>
    CFSG.EvenSporadicStandard.TwoCo1.card_centralizer_involution_of_isSporadic_co1 h hu
  card_pinned := by
    intro s hs T _ _ h
    simp only [pinnedNames, Sol78Rows, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | (obtain ⟨e⟩ := h
         exact (CFSG.SeitzReduction.RankOne.card_of_mulEquiv_nativeM e).trans
           (by norm_num [CFSG.Open.monsterOrder, pinnedOrder]))
      | exact (card_of_isSporadic_of_ne (by decide) (by decide) h).trans
          (by norm_num [CFSG.EvenSmallLie.Child3.sporadicCard, pinnedOrder,
            CFSG.Open.monsterBabyOrder])

end CFSG.EvenSporadicStandard.Induction.Hyp
