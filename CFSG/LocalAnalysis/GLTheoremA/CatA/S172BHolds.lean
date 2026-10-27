module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172Facts
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BOfModels
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BExist
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BFive

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172


theorem s172FactB_holds : S172FactB :=
  s172FactB_of_models CFSG.StandardType.ggLabelRigidInput_holds
    (fun _ _ _ _ _ _ hQ hdim hplus h7 hodd hbound =>
      S172B.modelExist_orthDerived hQ hdim hplus hbound h7 hodd
        CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds)
    (fun _ _ _ _ _ hQ hdim hplus hbound =>
      S172B.modelSolvable_orthDerived_five hQ hdim hplus hbound
        CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds)

end CFSG.LocalAnalysis.GLTheoremA.S172

end
