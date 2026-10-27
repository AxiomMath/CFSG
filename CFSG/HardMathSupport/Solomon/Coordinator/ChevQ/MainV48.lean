module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4CubeHyper
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenOA
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeCenAsm
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24D4T2Final
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV45

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


@[expose] def SeitzExcOpenResidual14 : Prop :=
  E8NegCLineRest ∧
    (E6ThreeF4Close.F4NonToralNegHyperplane ∧ E6ThreeF4Close.F4NonToralSplitHyperplane ∧
      E6ThreeInner.TwE6ToralNegTwo ∧ E6ThreeInner.TwE6InnerA2CaseTwo ∧ E6ThreeInner.TwE6InnerNoA2Two ∧
      SeitzExcOpenRest5.E7NonToralTwoRest ∧ SeitzExcOpenRest4.ThreeNonToralCubeRest .E8 TauCeti.LieTypeIndex.E8)

theorem seitzExcOpenResidual13_of_residual14 (h : SeitzExcOpenResidual14) : SeitzExcOpenResidual13 :=
  ⟨h.1, E6ThreeF4Close.e6F4CubeD4Two_of_negHyperplane h.2.1,
    E6ThreeF4Close.twE6F4CubeD4One_of_splitHyperplane h.2.2.1,
    E6ThreeInner.twE6InnerCubeGenAt_two_of_cases h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2⟩

theorem seitzE6ThreeConn_of_connFixed (h : E6Three.KSGen.TwE6ConnFixed 40) : SeitzE6ThreeConn :=
  ⟨E6Three.e6NotAll24Census_of_OA E6Three.e6Cen_OA, E6Three.twE6ConnGen_of_d5 h, E6Three.twE6EightGen, E6Three.d4t2ModelGen_holds⟩

theorem i271ChevQ_of_inputs_v48 (hres : SeitzExcOpenResidual14) (hE6 : E6Three.KSGen.TwE6ConnFixed 40) :
    I271ChevQ :=
  i271ChevQ_of_inputs_v45 (seitzExcOpenResidual13_of_residual14 hres) (seitzE6ThreeConn_of_connFixed hE6)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
