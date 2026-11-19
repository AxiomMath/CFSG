module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.OddInvProof.Main

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem oddInvInput_holds :
    ∀ {G : Type} [Group G] [Finite G] {a z : G} (_h : IsF5Type a z) (_hF3 : Vert Fusion3Facts a z)
      (_hOrb : Vert GzOrbitFacts a z) (_hCls : Vert GzClassFacts a z) (_hNo : Vert GzNoFacts a z)
      (_hY4a : Vert Y4aFacts a z) (_hSGz : Vert StructGzFacts a z) (_hPar : Vert ParityFacts a z)
      (_hT5 : Vert TableVFacts a z) (_hT7 : Vert TableVIIFacts a z),
      OddInvFacts a z :=
  fun _h _hF3 _hOrb _hCls _hNo _hY4a _hSGz _hPar _hT5 _hT7 =>
    oddInv_of_hyps _h _hF3 _hOrb _hCls _hNo _hY4a _hSGz _hPar _hT5 _hT7

end CFSG.EvenSporadicStandard.HNRecog.Section3
