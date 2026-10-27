module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FourBProof.Cases

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem fourB_of_hyps (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
    (hF3 : Vert Fusion3Facts a z) (hPic : Vert A8Pictures a z) (hPerp : Vert PerpFacts a z)
    (hT5 : Vert TableVFacts a z) : FourBFacts a z := by
  have H : FourBHyps a z := ⟨hI, h, hF1, hF2, hF3, hPic, hPerp, hT5⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact fourB_classes H (FourBPair.of_mem_orb4B hx)
  · intro x hx t ht
    exact fourB_case_i H (FourBPair.of_mem_orb4B hx) ht
  · intro x hx t ht
    exact fourB_case_ii H (FourBPair.of_mem_orb4B hx) ht
  · intro x hx t ht
    exact fourB_case_iii H (FourBPair.of_mem_orb4B hx) ht

end CFSG.EvenSporadicStandard.HNRecog.Section3
