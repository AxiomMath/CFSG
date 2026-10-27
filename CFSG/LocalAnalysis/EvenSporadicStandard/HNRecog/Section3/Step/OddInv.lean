module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.OddInvProof.Main

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem oddInvInput_holds :
    ∀ {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z) (hF3 : Vert Fusion3Facts a z)
      (hOrb : Vert GzOrbitFacts a z) (hCls : Vert GzClassFacts a z) (hNo : Vert GzNoFacts a z)
      (hY4a : Vert Y4aFacts a z) (hSGz : Vert StructGzFacts a z) (hPar : Vert ParityFacts a z)
      (hT5 : Vert TableVFacts a z) (hT7 : Vert TableVIIFacts a z),
      OddInvFacts a z :=
  fun h hF3 hOrb hCls hNo hY4a hSGz hPar hT5 hT7 =>
    oddInv_of_hyps h hF3 hOrb hCls hNo hY4a hSGz hPar hT5 hT7

end CFSG.EvenSporadicStandard.HNRecog.Section3
