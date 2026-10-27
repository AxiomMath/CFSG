module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableIIIProof.Main

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem tableIIIInput_holds :
    ∀ (hI : TwoHSInterface) (hS : SuborbitFacts) {G : Type} [Group G] [Finite G] {a z : G}
      (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
      (hF3 : Vert Fusion3Facts a z) (hPic : Vert A8Pictures a z) (hOrb : Vert GzOrbitFacts a z)
      (hSGz : Vert StructGzFacts a z) (hSX : Vert StructXFacts a z),
      TableIIIFacts a z := by
  intro hI hS G _ _ a z h hF1 hF2 hF3 hPic hOrb hSGz hSX
  exact tableIII_of_hyps hI hS h hF1 hF2 hF3 hPic hOrb hSGz hSX

end CFSG.EvenSporadicStandard.HNRecog.Section3
