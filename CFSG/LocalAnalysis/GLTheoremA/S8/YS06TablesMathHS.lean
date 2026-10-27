module

public import CFSG.LocalAnalysis.GLTheoremA.S8.YS06Cat11
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I66RealSuz
public import CFSG.LocalAnalysis.GLTheoremA.CatB.CfgIResAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.PumpingUpLeaves

public section

namespace CFSG.LocalAnalysis.GLTheoremA


theorem ys06SporTables2NoNine_holds : YS06SporTables2NoNine :=
  ⟨⟨i66RealS_holds,
      CFSG.HardMathSupport.Solomon.Coordinator.noOrderSixtyFiveBM_of_M
        CFSG.HardMathSupport.Dickson.Sec6.I1431.noOrder65_M⟩,
    S8.CfgI.cfgIRes_holds⟩

end CFSG.LocalAnalysis.GLTheoremA

end
