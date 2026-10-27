module

public import CFSG.HardMathSupport.Solomon.Coordinator.I19DefCharHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.I19_10AltThree

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance


theorem localTwoBalanceAltLow_holds : LocalTwoBalanceAltLow :=
  localTwoBalanceAltLow_of_three_five localTwoBalanceAltThree_proved localTwoBalanceAltFive_proved

theorem input19_6_9_of_open (hC : LocalTwoBalanceCrossCharThree)
    (hSp : LocalTwoBalanceSporadicThree) : Lemma25Ns.Input19_6_9 :=
  input19_6_9_of_families localTwoBalanceDefCharThree_holds hC hSp

theorem input19_10_of_open (h3 : CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeBalance)
    (h2 : LocalTwoBalanceGtFive) (hC3 : LocalTwoBalanceCrossCharThree)
    (hSp3 : LocalTwoBalanceSporadicThree) (hC5 : LocalTwoBalanceCrossCharFive)
    (hSp5 : LocalTwoBalanceSporadicFive) (hU38 : U3EightTwoBalanceThree)
    (hW3 : WeakLThreeEpsThree) (hFi : Fi22CoverFive) (hWFi : WeakFi22Five)
    (hWL5 : WeakLFiveEpsFive) (hE5 : LFiveEpsFiveTwo) : Input19_10 :=
  input19_10_of_parts h3 h2 localTwoBalanceAltLow_holds
    (localTwoBalanceSimpleThree_of_families localTwoBalanceDefCharThree_holds hC3 hSp3)
    (localTwoBalanceSimpleFive_of_families localTwoBalanceDefCharFive_holds hC5 hSp5)
    hU38 hW3 hFi hWFi hWL5 hE5

end CFSG.HardMathSupport.Solomon.Coordinator
