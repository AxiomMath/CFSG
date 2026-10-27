module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.Main

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem sixAInput_holds :
    ∀ {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z) (hF3 : Vert Fusion3Facts a z)
      (hPic : Vert A8Pictures a z) (hT5 : Vert TableVFacts a z) (hS7 : Vert S7Facts a z),
      SixAFacts a z := @sixA_of_hyps

end CFSG.EvenSporadicStandard.HNRecog.Section3
