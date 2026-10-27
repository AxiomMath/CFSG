module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalTwoRows
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6Six
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8TenTwelve
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicGtFiveRows

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Blueprint CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census

set_option linter.unusedSectionVars false


theorem localTwoBalanceSimpleGtFive_holds
    : LocalTwoBalanceSimpleGtFive :=
  localTwoBalanceSimpleGtFive_of_open_rows
    CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.innerPlaneBalanceAt_E6_six
    CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.innerPlaneBalanceAt_E8_ten
    CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.innerPlaneBalanceAt_E8_twelve
    CFSG.HardMathSupport.Dickson.LocalTwoBalance.sporadicTwoPairHolds_Fi24Prime_seven
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.oPrimeCoreLeTwoAt_B_seven
    CFSG.HardMathSupport.Dickson.LocalTwoBalance.sporadicTwoPairHolds_M_thirteen

end CFSG.HardMathSupport.Timmesfeld.Coordinator
