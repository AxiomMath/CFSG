module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Gz9.Main

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem gz9Input_holds :
    ∀ (_hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G} (_h : IsF5Type a z)
      (_hF2 : Vert Fusion2Facts a z) (_hF3 : Vert Fusion3Facts a z) (_hOrb : Vert GzOrbitFacts a z)
      (_hNo : Vert GzNoFacts a z) (_hY4a : Vert Y4aFacts a z),
      Gz9Facts a z := by
  intro _hC G _ _ a z _h _hF2 _hF3 _hOrb _hNo _hY4a
  exact gz9_of_hyps _hC _h _hF2 _hF3 _hOrb _hNo _hY4a

end CFSG.EvenSporadicStandard.HNRecog.Section3
