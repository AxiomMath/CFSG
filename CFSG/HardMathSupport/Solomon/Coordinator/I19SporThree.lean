module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.I19SporCrit
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_6Red
public import CFSG.HardMathSupport.Timmesfeld.Proving.SporadicOuterLeTwo
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.Blueprint

set_option linter.unusedSectionVars false

@[expose] def openNames3 : Finset TauCeti.SporadicName := {.M11, .M12, .M22, .M23, .J4, .HS, .He}


theorem sporadicTwoBalanceThree_J1 (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) :
    SporadicTwoBalanceThree .J1 := by
  intro S _ _ hS hnab he
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hcard : Nat.card S = 175560 := by
    rw [Nat.card_congr (he.some.trans (hbr .J1).some.symm).toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  exact i19s_vacuous Nat.prime_three (by norm_num) hcen (hOut S hS hnab .J1 he)
    (by rw [hcard]; norm_num)

theorem localTwoBalanceSporadicThree_of_open_names (hOne : SporadicOneParts)
    (hopen : ∀ name ∈ openNames3, SporadicTwoBalanceThree name) : LocalTwoBalanceSporadicThree := by
  have hbr : SporadicBridges := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hOut : SporadicOuterLeTwo := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  intro name
  have hcls : SporadicOnePair name 3 ∨ name = .M24 ∨ name = .J2 ∨ name = .Ru ∨ name = .J1 ∨
      name ∈ openNames3 := by
    unfold openNames3
    cases name <;> decide
  rcases hcls with h | rfl | rfl | rfl | rfl | h
  · intro S _ _ hS hnab he
    exact i19s_balanced_of_onePair Nat.prime_three (by norm_num) (hbr name) (hOne.holds name 3 h)
      hOut hS hnab he
  · intro S _ _ hS hnab he
    exact gapFinalBalance_holds S (Or.inl he)
  · intro S _ _ hS hnab he
    exact gapFinalBalance_holds S (Or.inr (Or.inl he))
  · intro S _ _ hS hnab he
    exact gapFinalBalance_holds S (Or.inr (Or.inr he))
  · exact sporadicTwoBalanceThree_J1 hbr hOut
  · exact hopen name h

end CFSG.HardMathSupport.Solomon.Coordinator
