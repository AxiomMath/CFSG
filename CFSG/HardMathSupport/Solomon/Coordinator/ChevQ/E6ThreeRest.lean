module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDiagParTw
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwFieldCube
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV31

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh

open CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDefs

section Rest

set_option linter.unusedSectionVars false


theorem seitzGoodOuterHighE6Three_of_nonPar (h₅ : E6DiagNonParCubes)
    (h₆ : TwE6DiagNonParCubes) : SeitzGoodOuterHighE6Three :=
  seitzGoodOuterHighE6Three_of_cubes (E6Three.e6FieldCubes_of_kfact kFactSeitzRankTwo_holds)
      (E6Three.twE6FieldCubes_of_kfact kFactSeitzRankTwo_holds) E6Three.e6DiagParCubes_holds
      E6Three.twE6DiagParCubes_holds h₅ h₆

theorem seitzE6ThreeRest_of_nonPar (h₅ : E6DiagNonParCubes) (h₆ : TwE6DiagNonParCubes) :
    SeitzE6ThreeRest :=
  ⟨seitzGoodOuterHighE6Three_of_nonPar h₅ h₆,
    twE6EightDiagCubes_of_cubes E6Three.twE6DiagParCubes_holds h₆⟩

end Rest

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh

end
