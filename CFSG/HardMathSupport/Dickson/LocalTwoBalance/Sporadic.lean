module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicThree.Assembly
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicThree.J4
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicFive.Assembly
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicFive.Fi24Prime
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.SporadicFive.Th

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance

open CFSG.HardMathSupport.Solomon.Coordinator

section Three


theorem localTwoBalanceSporadicThree_holds : LocalTwoBalanceSporadicThree :=
  localTwoBalanceSporadicThree_of_J4 sporadicTwoBalanceThree_J4

end Three

section Five


theorem localTwoBalanceSporadicFive_holds : LocalTwoBalanceSporadicFive :=
  localTwoBalanceSporadicFive_of_Fi24_Th sporadicTwoBalanceFive_Fi24Prime sporadicTwoBalanceFive_Th

end Five

end CFSG.HardMathSupport.Dickson.LocalTwoBalance
