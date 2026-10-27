module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2Five
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.I19SporCrit
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10Red
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.Blueprint

set_option linter.unusedSectionVars false

@[expose] def openNames5 : Finset TauCeti.SporadicName :=
  {.J2, .HS, .McL, .Suz, .He, .Ru, .Co3, .Fi23, .Fi24Prime, .Th}

@[expose] def vacuousNames5 : Finset TauCeti.SporadicName :=
  {.M11, .M12, .M22, .M23, .M24, .J1, .J3, .J4, .ONan}


theorem sporadicTwoBalanceFive_of_vacuous {name : TauCeti.SporadicName}
    (hname : name ∈ vacuousNames5) : SporadicTwoBalanceFive name := by
  have hbr : SporadicBridges := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hOut : SporadicOuterLeTwo := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  intro S _ _ hS hnab he
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  refine i19s_vacuous Nat.prime_five (by norm_num) hcen (hOut S hS hnab name he) fun h => ?_
  have hq : 5 ^ 2 ∣ Nat.card (NativeSporadic.Carrier name) := by
    rw [← Nat.card_congr (he.some.trans (hbr name).some.symm).toEquiv]
    exact h
  have hmem : name ∈ CFSG.RankThree.PartOne.Census3.sporadicsThm3 := by
    unfold vacuousNames5 at hname
    revert hname
    cases name <;> decide
  have hp := CFSG.RankThree.PartOne.CTP.sporadicPair_of_sq_dvd hmem (p := 5) (by norm_num)
    (by norm_num) hq
  revert hp hname
  unfold vacuousNames5 CFSG.RankThree.PartOne.CTP.SporadicPair
    CFSG.RankThree.PartOne.CTP.SporadicPairNC CFSG.RankThree.PartOne.CTP.SporadicPairAb
  cases name <;> simp

theorem localTwoBalanceSporadicFive_of_open_names (hOne : SporadicOneParts)
    (hopen : ∀ name ∈ openNames5, SporadicTwoBalanceFive name) : LocalTwoBalanceSporadicFive := by
  have hbr : SporadicBridges := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hOut : SporadicOuterLeTwo := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  intro name hne
  have hcls : SporadicOnePair name 5 ∨ name = .Co2 ∨ name ∈ vacuousNames5 ∨
      name ∈ openNames5 := by
    unfold openNames5 vacuousNames5
    revert hne
    cases name <;> decide
  rcases hcls with h | rfl | h | h
  · intro S _ _ hS hnab he
    exact i19s_balanced_of_onePair Nat.prime_five (by norm_num) (hbr name) (hOne.holds name 5 h)
      hOut hS hnab he
  · intro S _ _ hS hnab he
    exact i19s_balanced_of_onePair Nat.prime_five (by norm_num) (hbr .Co2)
      sporadicOnePairHolds_Co2_five hOut hS hnab he
  · exact sporadicTwoBalanceFive_of_vacuous h
  · exact hopen name h

end CFSG.HardMathSupport.Solomon.Coordinator
