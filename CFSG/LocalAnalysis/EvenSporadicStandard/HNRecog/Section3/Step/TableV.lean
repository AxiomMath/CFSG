module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVMain

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem tableVInput_holds :
    ∀ (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
      (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z)
      (hT3 : Vert TableIIIFacts a z) (hT4 : Vert TableIVFacts a z) (hPar : Vert ParityFacts a z)
      (hPerp : Vert PerpFacts a z),
      TableVFacts a z := by
  intro hI G _ _ a z h hF1 hF2 hF3 hT3 hT4 _ _
  exact tableV_of_hyps hI h hF1 hF2 hF3 hT3 hT4

end CFSG.EvenSporadicStandard.HNRecog.Section3
