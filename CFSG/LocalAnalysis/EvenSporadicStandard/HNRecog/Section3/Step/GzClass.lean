module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.InvTwoGz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem gzClassInput_holds :
    ∀ (hI : TwoHSInterface) (hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G}
      (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
      (hF3 : Vert Fusion3Facts a z) (hOrb : Vert GzOrbitFacts a z),
      GzClassFacts a z := by
  intro hI hC G _ _ a z h hF1 hF2 hF3 hOrb
  refine ⟨?_, ?_, ?_⟩
  · intro x hx hshape
    refine gzClass_centralizes_two_A hI hC h hF1 hF2 hF3 hOrb x hx ?_
    rcases hshape with hs | hs
    · exact Or.inl (card_of_isShapeZ2TimesA5 hs)
    · exact Or.inr (card_of_isShapeTwoTwoWrTwo hs)
  · intro x hx hshape
    exact gzClass_centQ_card hI hC h hF1 hF2 hF3 hOrb x hx (card_of_isShapeTwoTwoTimesA5 hshape)
  · exact fun t ht => gzClass_inv_two hI hC h hF1 hF2 hF3 hOrb t ht

end CFSG.EvenSporadicStandard.HNRecog.Section3
