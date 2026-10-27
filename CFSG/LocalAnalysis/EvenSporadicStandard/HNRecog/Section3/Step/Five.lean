module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.FiveE

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem five_of_core (hI : TwoHSInterface) (hU : U35Facts) {G : Type} [Group G] [Finite G]
    {a z : G} (h : IsF5Type a z) (hCore : Vert FiveCoreFacts a z) (hCls : Vert GzClassFacts a z)
    (hPar : Vert ParityFacts a z) (hT4 : Vert TableIVFacts a z) (hT5 : Vert TableVFacts a z)
    (hT6 : Vert TableVIFacts a z) (hT7 : Vert TableVIIFacts a z) (hGam : Vert GammaFacts a z) :
    FiveFacts a z :=
  { hCore.self with
    five_E := fun x hx =>
      isShapeFiveCubeByTwoTwo_of_orb5E hI hU h hCore hPar.self hCls.self hT4.self hT5.self hT6.self
        hT7.self hGam.self hx
    inv_cent := fun x hx t ht htρ =>
      mem_Gxy_of_orb5E hI hU h hCore hPar.self hCls.self hT4.self hT5.self hT6.self hT7.self
        hGam.self hx ht htρ
    klein_E := fun x hx =>
      exists_klein_of_orb5E hI hU h hCore hPar.self hCls.self hT4.self hT5.self hT6.self hT7.self
        hGam.self hx }

end CFSG.EvenSporadicStandard.HNRecog.Section3
