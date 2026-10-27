module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerPlane
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerFinal
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerGlue
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerWeyl
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerFix24
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerSylowLine
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeA2Conj
public import CFSG.LieType.SeitzGeneration.SeitzStatus

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.LieType.SeitzGeneration
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

section Composition

set_option linter.unusedSectionVars false


theorem e6InnerCubeGenAt_one_of_line (hLine : E6InnerSylowMonoLine) : E6InnerCubeGenAt 1 :=
  e6InnerCubeGenAt_one_of_conjGen
    (e6InnerOneConjGen_of_core kFactSeitzRankTwo_holds e6ThreeA2Conj_holds e6ThreeLayerGen_holds
      (e6InnerAll24Plane_of_pieces e6InnerSylowMono_holds hLine e6MonoFixNormalizes_holds
        e6WeylEllipticOfNoFixed_holds e6MonoEllipticFix24_holds e6ThreeA2Conj_holds
        e6ThreeA2Witness_holds))

theorem e6InnerCubeGenAt_one_holds : E6InnerCubeGenAt 1 :=
  e6InnerCubeGenAt_one_of_line e6InnerSylowMonoLine_holds

end Composition

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner
