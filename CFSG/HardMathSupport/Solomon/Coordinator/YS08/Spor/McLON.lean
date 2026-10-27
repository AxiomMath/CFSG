module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Numerics
public import CFSG.RankThree.PartTwo.KFacts.K426RestMcL
public import CFSG.RankThree.PartTwo.KFacts.K426RestON
public import CFSG.Sporadic.McL.Simple
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Solomon.Coordinator

theorem sporL3DownInner_McL
    (hbr : SporadicBridges) : SporL3DownInner .McL := by
  haveI : Finite NativeSporadic.McL := Nat.finite_of_card_ne_zero (by
    rw [CFSG.Sporadic.McL.card_McL]; norm_num)
  refine sporL3DownInner_of_comp NativeSporadic.McL (hbr .McL)
    (by rw [CFSG.Sporadic.McL.card_McL]; exact noL3Eq_898128000) ?_
  intro x hx
  refine noL3Comp_of_noDvd ?_
  rcases CFSG.RankThree.PartTwo.KFacts.K426Rest.mclThreeCentralizerCard x hx with h | h
  · rw [h]; exact noL3Dvd_29160
  · rw [h]; exact noL3Dvd_972

theorem sporL3DownInner_ONan
    (hbr : SporadicBridges) : SporL3DownInner .ONan := by
  haveI : Finite NativeSporadic.ON := Nat.finite_of_card_ne_zero (by
    rw [CFSG.Sporadic.ON.card_ON]; norm_num)
  refine sporL3DownInner_of_comp NativeSporadic.ON (hbr .ONan)
    (by rw [CFSG.Sporadic.ON.card_ON]; exact noL3Eq_460815505920) ?_
  intro x hx
  refine noL3Comp_of_noDvd ?_
  rw [CFSG.RankThree.PartTwo.KFacts.K426Rest.onThreeCentralizer x hx]
  exact noL3Dvd_3240

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
