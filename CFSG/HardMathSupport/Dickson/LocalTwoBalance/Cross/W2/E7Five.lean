module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7FiveAux.Plane

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross


theorem e7InnerFiveOne_holds : E7InnerFiveOne :=
  fun q hv _ h => W2.innerPlaneBalance_catE7_five_split q hv h

theorem e7InnerFiveTwo_holds : E7InnerFiveTwo :=
  fun q hv _ h => W2.innerPlaneBalance_catE7_five_neg q hv h

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
