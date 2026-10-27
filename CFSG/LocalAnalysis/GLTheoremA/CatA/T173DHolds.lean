module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XMain
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416ROdd
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173SplitHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173X


theorem i173FactD_of_mixed (hMixed : ModelFactMixedD) : T173.I173FactD :=
  i173FactD_of_models CFSG.StandardType.ggLabelRigidInput_holds
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds chev2OddAmb_holds
    T173S.modelFactSplit T173U.modelFactFrameD hMixed

theorem i173FactTD_of_mixed (hMixed : ModelFactMixedTD) : T173.I173FactTD :=
  i173FactTD_of_models CFSG.StandardType.ggLabelRigidInput_holds
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds chev2OddAmb_holds
    T173S.modelFactSplit T173U.modelFactFrameTD hMixed

theorem i173FactD_holds : T173.I173FactD :=
  i173FactD_of_mixed T173M.modelFactMixedD

theorem i173FactTD_holds : T173.I173FactTD :=
  i173FactTD_of_mixed T173M.modelFactMixedTD

end CFSG.LocalAnalysis.GLTheoremA.T173X

end
