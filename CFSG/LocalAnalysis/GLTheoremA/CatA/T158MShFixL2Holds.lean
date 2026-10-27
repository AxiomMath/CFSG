module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShFixL2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.L2CentFieldCube
public import CFSG.Adapters.Certificate43Check
public import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.LocalAnalysis.GLTheoremA

theorem l2cFieldCaseCube_holds : L2cFieldCaseCube := by
  intro Q _ _ n F _ _ hZ hF hn e a ha3 ha1 S hS
  exact l2c_field_case_cube hZ hF hn e (a := a) ha3 ha1 hS

theorem t158FixL2_holds : T158FixL2 :=
  t158FixL2_holds_of_cube l2cFieldCaseCube_holds

end CFSG.LocalAnalysis.GLTheoremA.T158

end
