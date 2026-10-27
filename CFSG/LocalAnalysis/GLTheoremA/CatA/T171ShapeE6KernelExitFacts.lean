module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6KernelExitWire
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSizeFact
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeAssemblyFinal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6NoAct
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLinUniBoundHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLowerLin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLowerUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLowerE6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh.KExit


theorem t171SizeFact_of_kernel (hK : ExcKernelCompAction) (hD4 : InnerD4FixedPointsPerfect) :
    T171.T171SizeFact :=
  t171SizeFact_of u6Type9_holds (e6Bound_of_kernel hK hD4 true)

theorem t171NoActFact_of_kernel (hK : ExcKernelCompAction) (hD4 : InnerD4FixedPointsPerfect) :
    T171.T171NoActFact :=
  t171NoActFact_of u6Type9_holds u6NoActModel_holds (twE6NoAct_of_kernel hK hD4)

theorem t171ShapeFact_of_kernel (hS : Shape15On fun _ => True) (hK : ExcKernelCompAction)
    (hD4 : InnerD4FixedPointsPerfect) : T171.T171ShapeFact :=
  t171ShapeFact_of hS linUniBound_holds (e6Bound_of_kernel hK hD4 false) lowerLin_holds
    lowerUni_holds lowerE6_holds

end CFSG.LocalAnalysis.GLTheoremA.T171Sh.KExit

end
