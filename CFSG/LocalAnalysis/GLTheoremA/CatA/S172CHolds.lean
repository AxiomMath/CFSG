module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172Facts
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172COfModels
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CExist

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172


theorem s172FactC_holds : S172FactC :=
  s172FactC_of_models CFSG.StandardType.ggLabelRigidInput_holds
    (fun _ _ _ _ _ _ _ _ _ _ _ hQ hdim hminus hn heven hp hp2 hpq hbound =>
      S172C.modelExist_orthDerived_minus hQ hdim hp hp2 hpq hbound hminus hn heven
        CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds)

end CFSG.LocalAnalysis.GLTheoremA.S172

end
