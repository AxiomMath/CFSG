module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Gz9.Main

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem gz9Input_holds :
    ∀ (hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
      (hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z) (hOrb : Vert GzOrbitFacts a z)
      (hNo : Vert GzNoFacts a z) (hY4a : Vert Y4aFacts a z),
      Gz9Facts a z := by
  intro hC G _ _ a z h hF2 hF3 hOrb hNo hY4a
  exact gz9_of_hyps hC h hF2 hF3 hOrb hNo hY4a

end CFSG.EvenSporadicStandard.HNRecog.Section3
