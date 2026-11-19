module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGzProof.Main

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem structGzInput_holds :
    ∀ (_hI : TwoHSInterface) (_hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G}
      (_h : IsF5Type a z) (_hF1 : Vert Fusion1Facts a z) (_hF2 : Vert Fusion2Facts a z)
      (_hF3 : Vert Fusion3Facts a z) (_hPic : Vert A8Pictures a z) (_hOrb : Vert GzOrbitFacts a z)
      (_hCls : Vert GzClassFacts a z) (_hY4a : Vert Y4aFacts a z) (_hGz9 : Vert Gz9Facts a z),
      StructGzFacts a z := by
  intro _hI _hC G _ _ a z _h _hF1 _hF2 _hF3 _hPic _hOrb _hCls _hY4a _hGz9
  exact structGz_of_hyps _hI _hC _h _hF1 _hF2 _hF3 _hPic _hOrb _hCls _hY4a _hGz9

end CFSG.EvenSporadicStandard.HNRecog.Section3
