module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FiveAux.Plane

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross


theorem e6InnerFiveOne_holds : E6InnerFiveOne :=
  fun q hv _ h => W2.innerPlaneBalance_catE6_five_split q hv h

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
