module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.S7Shapes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem s7_of_hyps {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
    (hCube : Vert CubeFacts a z) (hF3 : Vert Fusion3Facts a z) (hPic : Vert A8Pictures a z)
    (hPar : Vert ParityFacts a z) (hT4 : Vert TableIVFacts a z) (hPerp : Vert PerpFacts a z)
    (hT5 : Vert TableVFacts a z) (h4B : Vert FourBFacts a z) : S7Facts a z := by
  have _ := h4B
  have H : S7Hyps a z := ⟨h, hCube, hF3, hPic, hPar, hT4, hPerp, hT5⟩
  exact ⟨s7_orbit H, fun x hx => s7_shape H hx, fun x hx => s7_classes H hx,
    fun x hx t ht => s7_shape_i H hx ht, fun x hx t ht => s7_shape_ii H hx ht,
    fun x hx t ht => s7_shape_iii H hx ht, s7_cycleType H⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
