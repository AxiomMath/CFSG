module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Main

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem s7Input_holds :
    ∀ {G : Type} [Group G] [Finite G] {a z : G} (_h : IsF5Type a z) (_hCube : Vert CubeFacts a z)
      (_hF3 : Vert Fusion3Facts a z) (_hPic : Vert A8Pictures a z) (_hPar : Vert ParityFacts a z)
      (_hT4 : Vert TableIVFacts a z) (_hPerp : Vert PerpFacts a z) (_hT5 : Vert TableVFacts a z)
      (_h4B : Vert FourBFacts a z),
      S7Facts a z := @s7_of_hyps

end CFSG.EvenSporadicStandard.HNRecog.Section3
