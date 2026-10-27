module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.MainV44
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoFinal
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeF4CubeGlue
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Assembly

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Dickson.I271
  CFSG.LieType.Seitz CFSG.AGLEmbeddingD2 CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding

set_option linter.unusedSectionVars false


@[expose] def SeitzExcOpenResidual13 : Prop :=
  E8NegCLineRest ∧
    (E6ThreeF4Close.E6F4CubeD4Two ∧ E6ThreeF4Close.TwE6F4CubeD4One ∧ E6ThreeInner.TwE6InnerCubeGenAt 2 ∧
      SeitzExcOpenRest5.E7NonToralTwoRest ∧ SeitzExcOpenRest4.ThreeNonToralCubeRest .E8 TauCeti.LieTypeIndex.E8)

@[expose] def SeitzE6ThreeConn : Prop :=
  E6Three.E6NotAll24Census ∧ E6Three.TwE6ConnGen ∧ E6Three.TwE6EightGen ∧ E6Three.D4T2ModelGen

theorem seitzExcOpenResidual12_of_residual13 (hres : SeitzExcOpenResidual13) : SeitzExcOpenResidual12 :=
  ⟨⟨hres.1, E6ThreeF4Close.e6InnerCubeGenAt_two_of_d4 threeNonToralCubeRest_F4_holds hres.2.1,
      E6ThreeInner.seitzGoodInnerExcThreeTwE6_of_cubes (E6ThreeInner.twE6InnerCubeGen_of_at
        (E6ThreeF4Close.twE6InnerCubeGenAt_one_of_d4 threeNonToralCubeRest_F4_holds hres.2.2.1) hres.2.2.2.1),
      hres.2.2.2.2.1, hres.2.2.2.2.2⟩,
    KSE8Five.e8TwoFiveNonToral_holds⟩

theorem seitzE6ThreeCensusTw_of_conn (h : SeitzE6ThreeConn) : SeitzE6ThreeCensusTw :=
  ⟨h.1, E6Three.twE6NotAll24Gen_of_gen h.2.1 h.2.2.1 h.2.2.2⟩

theorem i271ChevQ_of_inputs_v45 (hres : SeitzExcOpenResidual13) (hE6 : SeitzE6ThreeConn) : I271ChevQ :=
  i271ChevQ_of_inputs_v44 (seitzExcOpenResidual12_of_residual13 hres) (seitzE6ThreeCensusTw_of_conn hE6)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
