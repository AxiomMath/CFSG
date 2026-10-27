module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19_5_2M22
public import CFSG.HardMathSupport.Solomon.Coordinator.I19SporFinal
public import CFSG.HardMathSupport.Solomon.Coordinator.I19SporOne
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Fuse
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAClose
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBFinal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicThree.M12
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicThree.HS
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicThree.He

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator


private theorem sporadicTwoBalanceThree_M22 : SporadicTwoBalanceThree .M22 := by
  intro S _ _ _ _ ⟨e⟩
  exact IsLocallyBalancedAbs.of_mulEquiv e isLocallyBalancedAbs_M22

theorem localTwoBalanceSporadicThree_of_J4 (hJ4 : SporadicTwoBalanceThree .J4) :
    LocalTwoBalanceSporadicThree :=
  localTwoBalanceSporadicThree_of_open (sporadicOneParts_of_open
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.bThreeRc_holds
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.bThreeRd_holds
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.bFiveNonCentral_holds
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.twoAPureKlein_three_Gmat
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat.twoATwoCommuting_five_Gmat
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus.monsterSevenClasses) fun name hname => by
    have hcls : name = .M12 ∨ name = .M22 ∨ name = .J4 ∨ name = .HS ∨ name = .He := by
      unfold openNames3' at hname
      revert hname
      cases name <;> decide
    rcases hcls with rfl | rfl | rfl | rfl | rfl
    · exact sporadicTwoBalanceThree_M12
    · exact sporadicTwoBalanceThree_M22
    · exact hJ4
    · exact sporadicTwoBalanceThree_HS
    · exact sporadicTwoBalanceThree_He

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
