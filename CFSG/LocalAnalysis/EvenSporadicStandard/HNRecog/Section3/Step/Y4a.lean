module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.Main

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem y4aInput_holds :
    ∀ (_hI : TwoHSInterface) (_hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G}
      (_h : IsF5Type a z) (_hF1 : Vert Fusion1Facts a z) (_hCube : Vert CubeFacts a z)
      (_hA8 : Vert A8Shapes a z) (_hF2 : Vert Fusion2Facts a z) (_hF3 : Vert Fusion3Facts a z)
      (_hPic : Vert A8Pictures a z) (_hOrb : Vert GzOrbitFacts a z) (_hCls : Vert GzClassFacts a z),
      Y4aFacts a z := by
  intro _hI _hC G _ _ a z _h _hF1 _hCube _hA8 _hF2 _hF3 _hPic _hOrb _hCls
  exact y4a_of_hyps _hI _hC _h _hF1 _hCube _hA8 _hF2 _hF3 _hPic _hOrb _hCls

end CFSG.EvenSporadicStandard.HNRecog.Section3
