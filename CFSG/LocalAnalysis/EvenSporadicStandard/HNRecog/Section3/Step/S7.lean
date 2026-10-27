module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Main

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem s7Input_holds :
    ∀ {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z) (hCube : Vert CubeFacts a z)
      (hF3 : Vert Fusion3Facts a z) (hPic : Vert A8Pictures a z) (hPar : Vert ParityFacts a z)
      (hT4 : Vert TableIVFacts a z) (hPerp : Vert PerpFacts a z) (hT5 : Vert TableVFacts a z)
      (h4B : Vert FourBFacts a z),
      S7Facts a z := @s7_of_hyps

end CFSG.EvenSporadicStandard.HNRecog.Section3
