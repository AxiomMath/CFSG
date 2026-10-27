module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SuborbitFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GraphLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Orbits
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

structure GammaHyps {G : Type} [Group G] (a z : G) : Prop where
  h27 : Segev27
  hU : U35Facts
  h : IsF5Type a z
  hF1 : Vert Fusion1Facts a z
  hF2 : Vert Fusion2Facts a z
  hF3 : Vert Fusion3Facts a z
  hCube : Vert CubeFacts a z
  hOrb : Vert GzOrbitFacts a z
  hCls : Vert GzClassFacts a z
  hNo : Vert GzNoFacts a z
  hPar : Vert ParityFacts a z
  hT4 : Vert TableIVFacts a z
  hPerp : Vert PerpFacts a z
  hT5 : Vert TableVFacts a z
  h4B : Vert FourBFacts a z
  h6A : Vert SixAFacts a z
  hT7 : Vert TableVIIFacts a z
  hLines : Vert LinesFacts a z
  hOdd : Vert OddInvFacts a z

theorem GammaHyps.of_isConj {G : Type} [Group G] {a z x w : G} (H : GammaHyps a z)
    (hx : IsConj a x) (hw : IsConj z w) : GammaHyps x w where
  h27 := H.h27
  hU := H.hU
  h := isF5Type_of_isConj H.h hx hw
  hF1 := H.hF1.of_isConj hx hw
  hF2 := H.hF2.of_isConj hx hw
  hF3 := H.hF3.of_isConj hx hw
  hCube := H.hCube.of_isConj hx hw
  hOrb := H.hOrb.of_isConj hx hw
  hCls := H.hCls.of_isConj hx hw
  hNo := H.hNo.of_isConj hx hw
  hPar := H.hPar.of_isConj hx hw
  hT4 := H.hT4.of_isConj hx hw
  hPerp := H.hPerp.of_isConj hx hw
  hT5 := H.hT5.of_isConj hx hw
  h4B := H.h4B.of_isConj hx hw
  h6A := H.h6A.of_isConj hx hw
  hT7 := H.hT7.of_isConj hx hw
  hLines := H.hLines.of_isConj hx hw
  hOdd := H.hOdd.of_isConj hx hw

end CFSG.EvenSporadicStandard.HNRecog.Section3
