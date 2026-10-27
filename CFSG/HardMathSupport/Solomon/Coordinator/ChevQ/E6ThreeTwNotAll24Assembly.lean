module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Main
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EvenFinal
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24EightComps

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

set_option linter.unusedSectionVars false

theorem twE6NotAll24Gen_of_gen (hConnGen : TwE6ConnGen) (hEightGen : TwE6EightGen)
    (hD4 : D4T2ModelGen) : TwE6NotAll24Gen :=
  twE6NotAll24Gen_of_eight
    (twE6EightA1A4_of_comps CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds hEightGen
      KSEight.twE6EightComps)
    (twE6LineStructure'_of_types twE6Order3Dim_holds (twE6LineStructureD4In_of_model hD4)
      (twE6LineStructureD4Out_of_model hD4) KSNotAll24.twE6LineStructureA2Out_holds
      (twE6LineStructureA5_of_residuals twE6ConnCentre twE6ConnShapeEven hConnGen)
      (twE6LineStructureA1A4_of_residuals twE6ConnCentre twE6ConnShapeEven hConnGen)
      (twE6LineStructureD5_of_residuals twE6ConnCentre twE6ConnShapeEven hConnGen))

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
