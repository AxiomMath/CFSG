module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV48
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoToralNeg
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseI
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoFrameH0
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseII

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


@[expose] def SeitzExcOpenResidual15 : Prop :=
  E8NegCLineRest ∧
    (E6ThreeF4Close.F4NonToralNegHyperplane ∧ E6ThreeF4Close.F4NonToralSplitHyperplane ∧
      E6ThreeInner.TwE6CaseIFrameH0 ∧ E6ThreeInner.TwE6CaseIICycNonA2 ∧ E6ThreeInner.TwE6CaseIIRankTwo ∧
      SeitzExcOpenRest5.E7NonToralTwoRest ∧ SeitzExcOpenRest4.ThreeNonToralCubeRest .E8 TauCeti.LieTypeIndex.E8)

theorem seitzExcOpenResidual14_of_residual15 (h : SeitzExcOpenResidual15) : SeitzExcOpenResidual14 :=
  ⟨h.1, h.2.1, h.2.2.1,
    E6ThreeInner.twE6ToralNegTwo_of_regularLangNeg E6ThreeInner.twE6RegularLangNeg_of_cert,
    E6ThreeInner.twE6InnerA2CaseTwo_of_frameH0 E6ThreeInner.twE6SylowMonoTwoAt_holds h.2.2.2.1,
    E6ThreeInner.twE6InnerNoA2Two_of_cycNonA2_rankTwo h.2.2.2.2.1 h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2⟩

theorem i271ChevQ_of_inputs_v49 (hres : SeitzExcOpenResidual15) (hE6 : E6Three.KSGen.TwE6ConnFixed 40) :
    I271ChevQ :=
  i271ChevQ_of_inputs_v48 (seitzExcOpenResidual14_of_residual15 hres) hE6

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
