module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpMain

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem perpInput_holds :
    ∀ (_hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G} (_h : IsF5Type a z)
      (_hF1 : Vert Fusion1Facts a z) (_hF2 : Vert Fusion2Facts a z) (_hF3 : Vert Fusion3Facts a z)
      (_hPic : Vert A8Pictures a z) (_hT3 : Vert TableIIIFacts a z) (_hT4 : Vert TableIVFacts a z)
      (_hPar : Vert ParityFacts a z),
      PerpFacts a z := by
  intro _hI G _ _ a z _h _hF1 _hF2 _hF3 _hPic _hT3 _hT4 _hPar
  exact perp_of_hyps _hI _h _hF1 _hF2 _hF3 _hPic _hT3 _hT4 _hPar

end CFSG.EvenSporadicStandard.HNRecog.Section3
