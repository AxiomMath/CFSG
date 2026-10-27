module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Y4a.Main

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem y4aInput_holds :
    ∀ (hI : TwoHSInterface) (hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G}
      (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hCube : Vert CubeFacts a z)
      (hA8 : Vert A8Shapes a z) (hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z)
      (hPic : Vert A8Pictures a z) (hOrb : Vert GzOrbitFacts a z) (hCls : Vert GzClassFacts a z),
      Y4aFacts a z := by
  intro hI hC G _ _ a z h hF1 hCube hA8 hF2 hF3 hPic hOrb hCls
  exact y4a_of_hyps hI hC h hF1 hCube hA8 hF2 hF3 hPic hOrb hCls

end CFSG.EvenSporadicStandard.HNRecog.Section3
