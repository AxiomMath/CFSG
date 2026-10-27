module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwLayerGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwTorusGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwDec
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwFixedNC
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwToral
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwOuterHeis

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

set_option linter.unusedSectionVars false

section Holds


theorem twE6ThreeTorusGen_holds : TwE6ThreeTorusGen :=
  twE6ThreeTorusGen_of_model twTorusModel_holds


theorem twE6ThreeLayerGen_holds : TwE6ThreeLayerGen :=
  twE6ThreeLayerGen_of_model (twLayerModel_of_torusModel twTorusModel_holds)
    twFixedNonCentral_holds twToralPlane_holds twInnerHeisPlane_holds twOuterHeisPlane_holds

end Holds

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
