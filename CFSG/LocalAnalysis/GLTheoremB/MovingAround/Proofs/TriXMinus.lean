module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311y
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311z

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.TriXMinus


theorem frameCoreTransvection_holds : Inputs2311y.FrameCoreTransvection :=
  fun _ _ hℓ hℓ2 hℓ3 hf hq _ _ _ hK σ hσ Φ _ _ hxT hyT hx3 hx1 hy3 hyx =>
    Inputs2311z.exists_frame_core_transvection_inputs2311z hℓ hℓ2 hℓ3 hf hq hK σ hσ Φ hxT hyT hx3 hx1 hy3
      hyx

theorem triXNoGCentUniPlanesAt_two_holds : TriXPlus.TriXNoGCentUniPlanesAt 2 :=
  Inputs2311y.triXNoGCentUniPlanesAt_two_of_core frameCoreTransvection_holds

theorem triXNoGCentUniPlanes_of_at_one (h1 : TriXPlus.TriXNoGCentUniPlanesAt 1) :
    Inputs2311t.TriXNoGCentUniPlanes :=
  TriXPlus.triXNoGCentUniPlanes_of_at h1 triXNoGCentUniPlanesAt_two_holds

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.TriXMinus
