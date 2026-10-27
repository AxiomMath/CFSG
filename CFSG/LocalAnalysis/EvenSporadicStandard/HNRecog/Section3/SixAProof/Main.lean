module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.Classes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.Cases
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem sixA_of_hyps {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
    (_hF3 : Vert Fusion3Facts a z) (_hPic : Vert A8Pictures a z) (hT5 : Vert TableVFacts a z)
    (hS7 : Vert S7Facts a z) : SixAFacts a z :=
  { classes := fun _ hx => sixA_classes h hT5.self hS7.self hx
    case_i := fun _ hx _ ht => sixA_case_i h hT5.self hS7.self hx ht
    case_ii := fun _ hx _ ht => sixA_case_ii h hT5.self hS7.self hx ht }

end CFSG.EvenSporadicStandard.HNRecog.Section3
