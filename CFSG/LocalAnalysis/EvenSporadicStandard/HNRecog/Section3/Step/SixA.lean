module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.Main

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem sixAInput_holds :
    ∀ {G : Type} [Group G] [Finite G] {a z : G} (_h : IsF5Type a z) (_hF3 : Vert Fusion3Facts a z)
      (_hPic : Vert A8Pictures a z) (_hT5 : Vert TableVFacts a z) (_hS7 : Vert S7Facts a z),
      SixAFacts a z := @sixA_of_hyps

end CFSG.EvenSporadicStandard.HNRecog.Section3
