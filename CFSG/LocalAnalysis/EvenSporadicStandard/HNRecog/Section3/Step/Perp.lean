module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpMain

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem perpInput_holds :
    ∀ (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
      (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z)
      (hPic : Vert A8Pictures a z) (hT3 : Vert TableIIIFacts a z) (hT4 : Vert TableIVFacts a z)
      (hPar : Vert ParityFacts a z),
      PerpFacts a z := by
  intro hI G _ _ a z h hF1 hF2 hF3 hPic hT3 hT4 hPar
  exact perp_of_hyps hI h hF1 hF2 hF3 hPic hT3 hT4 hPar

end CFSG.EvenSporadicStandard.HNRecog.Section3
