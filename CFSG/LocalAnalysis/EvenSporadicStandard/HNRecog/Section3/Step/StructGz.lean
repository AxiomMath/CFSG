module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGzProof.Main

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem structGzInput_holds :
    ∀ (hI : TwoHSInterface) (hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G}
      (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
      (hF3 : Vert Fusion3Facts a z) (hPic : Vert A8Pictures a z) (hOrb : Vert GzOrbitFacts a z)
      (hCls : Vert GzClassFacts a z) (hY4a : Vert Y4aFacts a z) (hGz9 : Vert Gz9Facts a z),
      StructGzFacts a z := by
  intro hI hC G _ _ a z h hF1 hF2 hF3 hPic hOrb hCls hY4a hGz9
  exact structGz_of_hyps hI hC h hF1 hF2 hF3 hPic hOrb hCls hY4a hGz9

end CFSG.EvenSporadicStandard.HNRecog.Section3
