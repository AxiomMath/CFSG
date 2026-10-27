module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV41
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerOne
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlane

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


@[expose] def SeitzThreeResidual8 : Prop :=
  (E7NegCLineRest ∧ E8NegCLineRest) ∧
    (SeitzExcOpenRest4.ThreeNonToralCubeRest .F4 TauCeti.LieTypeIndex.F4 ∧ E6ThreeInner.E6InnerCubeGenAt 2 ∧
      SeitzExcOpenRest4.SeitzGoodInnerExcThreeTwE6 ∧ SeitzExcOpenRest5.E7NonToralTwoRest ∧
        SeitzExcOpenRest4.ThreeNonToralCubeRest .E8 TauCeti.LieTypeIndex.E8)

@[expose] def SeitzExcOpenResidual10 : Prop :=
  SeitzThreeResidual8 ∧ KSE8Five.E8TwoFiveNonToral

@[expose] def SeitzE6ThreeCensusTw : Prop :=
  E6Three.E6NotAll24Census ∧ E6Three.TwE6NotAll24Gen

theorem seitzExcOpenResidual9_of_residual10 (hres : SeitzExcOpenResidual10) : SeitzExcOpenResidual9 :=
  ⟨⟨hres.1.1, hres.1.2.1, E6ThreeInner.seitzGoodInnerExcThreeE6_of_cubes
      (E6ThreeInner.e6InnerCubeGen_of_at E6ThreeInner.e6InnerCubeGenAt_one_holds hres.1.2.2.1), hres.1.2.2.2⟩,
    hres.2⟩

theorem seitzE6ThreeTwo_of_censusTw (h : SeitzE6ThreeCensusTw) : SeitzE6ThreeTwo :=
  ⟨E6Three.e6ThreeNotAll24NFA_of_census h.1, h.2⟩

theorem i271ChevQ_of_inputs_v42 (hres : SeitzExcOpenResidual10) (hE6 : SeitzE6ThreeCensusTw) : I271ChevQ :=
  i271ChevQ_of_inputs_v41 (seitzExcOpenResidual9_of_residual10 hres) (seitzE6ThreeTwo_of_censusTw hE6)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
