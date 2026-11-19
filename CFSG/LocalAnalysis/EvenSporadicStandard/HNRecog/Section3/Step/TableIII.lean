module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.Main

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem tableIIIInput_holds :
    ∀ (_hI : TwoHSInterface) (_hS : SuborbitFacts) {G : Type} [Group G] [Finite G] {a z : G}
      (_h : IsF5Type a z) (_hF1 : Vert Fusion1Facts a z) (_hF2 : Vert Fusion2Facts a z)
      (_hF3 : Vert Fusion3Facts a z) (_hPic : Vert A8Pictures a z) (_hOrb : Vert GzOrbitFacts a z)
      (_hSGz : Vert StructGzFacts a z) (_hSX : Vert StructXFacts a z),
      TableIIIFacts a z := by
  intro _hI _hS G _ _ a z _h _hF1 _hF2 _hF3 _hPic _hOrb _hSGz _hSX
  exact tableIII_of_hyps _hI _hS _h _hF1 _hF2 _hF3 _hPic _hOrb _hSGz _hSX

end CFSG.EvenSporadicStandard.HNRecog.Section3
