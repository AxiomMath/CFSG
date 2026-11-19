module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.InvTwoGz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem gzClassInput_holds :
    ∀ (_hI : TwoHSInterface) (_hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G}
      (_h : IsF5Type a z) (_hF1 : Vert Fusion1Facts a z) (_hF2 : Vert Fusion2Facts a z)
      (_hF3 : Vert Fusion3Facts a z) (_hOrb : Vert GzOrbitFacts a z),
      GzClassFacts a z := by
  intro _hI _hC G _ _ a z _h _hF1 _hF2 _hF3 _hOrb
  refine ⟨?_, ?_, ?_⟩
  · intro x hx hshape
    refine gzClass_centralizes_two_A _hI _hC _h _hF1 _hF2 _hF3 _hOrb x hx ?_
    rcases hshape with hs | hs
    · exact Or.inl (card_of_isShapeZ2TimesA5 hs)
    · exact Or.inr (card_of_isShapeTwoTwoWrTwo hs)
  · intro x hx hshape
    exact gzClass_centQ_card _hI _hC _h _hF1 _hF2 _hF3 _hOrb x hx (card_of_isShapeTwoTwoTimesA5 hshape)
  · exact fun t ht => gzClass_inv_two _hI _hC _h _hF1 _hF2 _hF3 _hOrb t ht

end CFSG.EvenSporadicStandard.HNRecog.Section3
