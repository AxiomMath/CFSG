module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcTwistedHigh
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcTwistedE6

public section

namespace CFSG.HardMathSupport.Dickson.Sec6


theorem up34Chev2Leaf_holds : Up34Chev2Leaf :=
  up34Chev2Leaf_of_residuals (Up34Exc.char2Hrat_twoD _) (Up34Exc.char2Hrat_exc _)
    (Up34Exc.char2Hrat_twoD _) (Up34Exc.char2Hrat_exc _) (Up34Exc.char2Hrat_twoD _)
    (Up34Exc.char2Hrat_exc _)

end CFSG.HardMathSupport.Dickson.Sec6
