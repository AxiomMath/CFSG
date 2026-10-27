module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19SporFive
public import CFSG.HardMathSupport.Solomon.Coordinator.I19SporOne
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Fuse
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAClose
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBFinal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicFive.J2
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicFive.Co3
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicFive.Fi23
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicFive.McL
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicFive.He
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicFive.Ru
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicFive.Suz

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.HardMathSupport.Solomon.Coordinator


theorem localTwoBalanceSporadicFive_of_Fi24_Th (hFi24 : SporadicTwoBalanceFive .Fi24Prime)
    (hTh : SporadicTwoBalanceFive .Th) : LocalTwoBalanceSporadicFive :=
  localTwoBalanceSporadicFive_of_open_names (sporadicOneParts_of_open
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.bThreeRc_holds
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.bThreeRd_holds
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.bFiveNonCentral_holds
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF.twoAPureKlein_three_Gmat
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat.twoATwoCommuting_five_Gmat
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenCensus.monsterSevenClasses) fun name hname => by
    have hcls : name = .J2 ∨ name = .HS ∨ name = .McL ∨ name = .Suz ∨ name = .He ∨ name = .Ru ∨
        name = .Co3 ∨ name = .Fi23 ∨ name = .Fi24Prime ∨ name = .Th := by
      unfold openNames5 at hname
      revert hname
      cases name <;> decide
    rcases hcls with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact sporadicTwoBalanceFive_J2
    · exact sporadicTwoBalanceFive_HS
    · exact sporadicTwoBalanceFive_McL
    · exact sporadicTwoBalanceFive_Suz
    · exact sporadicTwoBalanceFive_He
    · exact sporadicTwoBalanceFive_Ru
    · exact sporadicTwoBalanceFive_Co3
    · exact sporadicTwoBalanceFive_Fi23
    · exact hFi24
    · exact hTh

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
