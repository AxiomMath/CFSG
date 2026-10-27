module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6KernelExit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralCoreKer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralLangTw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralH360
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralCoreUntwTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralExit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralExitUntw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6BoundToral
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6NoAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6Mark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6Mark

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh.KExit


theorem twE6W0TorusExit_of_kernel (hK : ExcKernelCompAction)
    (hD4 : InnerD4FixedPointsPerfect) : TwE6W0TorusExit :=
  twE6W0TorusExit_of_toralComponentAction
    (twE6W0ToralComponentAction_of_kernel hK twE6ToralLangSetup_holds
      (twE6ToralKernelExit_of hD4) twE6ToralLangSetupH360_holds)

theorem e6LangTorusExit_of_kernel (hK : ExcKernelCompAction)
    (hD4 : InnerD4FixedPointsPerfect) : E6LangTorusExit :=
  e6LangTorusExit_of_toralComponentAction
    (e6ToralComponentAction_of_kernel hK e6ToralLangSetup_holds
      (e6ToralKernelExit_of hD4) e6ToralLangSetupH360_holds)

theorem twE6NoAct_of_kernel (hK : ExcKernelCompAction) (hD4 : InnerD4FixedPointsPerfect) :
    TwE6NoAct :=
  twE6NoAct_of twE6Marking_holds (twE6BigToralExit_of (twE6W0TorusExit_of_kernel hK hD4))

theorem e6Bound_of_kernel (hK : ExcKernelCompAction) (hD4 : InnerD4FixedPointsPerfect)
    (tw : Bool) : E6Bound tw :=
  e6Bound_of twE6Marking_holds (twE6BigToralExit_of (twE6W0TorusExit_of_kernel hK hD4))
    e6Marking_holds (e6BigToralExit_of (e6LangTorusExit_of_kernel hK hD4)) tw

end CFSG.LocalAnalysis.GLTheoremA.T171Sh.KExit

end
