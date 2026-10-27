module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6FiveAux.TwPlane

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross


theorem twistedE6InnerFiveTwo_holds : TwistedE6InnerFiveTwo :=
  fun q hv _ h => W2.innerPlaneBalance_catTwistedE6_five_neg q hv h

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
