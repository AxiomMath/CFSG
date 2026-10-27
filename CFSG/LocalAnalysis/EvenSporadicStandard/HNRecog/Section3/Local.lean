module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Orbits
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GraphLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FiveLocal

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

structure F5Local (G : Type) [Group G] (a z : G) : Prop where
  fusion1 : Vert Fusion1Facts a z
  cube : Vert CubeFacts a z
  a8shapes : Vert A8Shapes a z
  fusion2 : Vert Fusion2Facts a z
  fusion3 : Vert Fusion3Facts a z
  a8pictures : Vert A8Pictures a z
  gzOrbit : Vert GzOrbitFacts a z
  gzClass : Vert GzClassFacts a z
  gzNo : Vert GzNoFacts a z
  y4a : Vert Y4aFacts a z
  gz9 : Vert Gz9Facts a z
  structGz : Vert StructGzFacts a z
  structX : Vert StructXFacts a z
  tableIII : Vert TableIIIFacts a z
  parity : Vert ParityFacts a z
  tableIV : Vert TableIVFacts a z
  perp : Vert PerpFacts a z
  tableV : Vert TableVFacts a z
  fourB : Vert FourBFacts a z
  s7 : Vert S7Facts a z
  sixA : Vert SixAFacts a z
  tableVI : Vert TableVIFacts a z
  tableVII : Vert TableVIIFacts a z
  lines : Vert LinesFacts a z
  oddInv : Vert OddInvFacts a z
  gamma : Vert GammaFacts a z
  five : Vert FiveFacts a z
  order : OrderFacts G

theorem F5Local.of_isConj {G : Type} [Group G] {a z x w : G} (h : F5Local G a z)
    (hx : IsConj a x) (hw : IsConj z w) : F5Local G x w where
  fusion1 := h.fusion1.of_isConj hx hw
  cube := h.cube.of_isConj hx hw
  a8shapes := h.a8shapes.of_isConj hx hw
  fusion2 := h.fusion2.of_isConj hx hw
  fusion3 := h.fusion3.of_isConj hx hw
  a8pictures := h.a8pictures.of_isConj hx hw
  gzOrbit := h.gzOrbit.of_isConj hx hw
  gzClass := h.gzClass.of_isConj hx hw
  gzNo := h.gzNo.of_isConj hx hw
  y4a := h.y4a.of_isConj hx hw
  gz9 := h.gz9.of_isConj hx hw
  structGz := h.structGz.of_isConj hx hw
  structX := h.structX.of_isConj hx hw
  tableIII := h.tableIII.of_isConj hx hw
  parity := h.parity.of_isConj hx hw
  tableIV := h.tableIV.of_isConj hx hw
  perp := h.perp.of_isConj hx hw
  tableV := h.tableV.of_isConj hx hw
  fourB := h.fourB.of_isConj hx hw
  s7 := h.s7.of_isConj hx hw
  sixA := h.sixA.of_isConj hx hw
  tableVI := h.tableVI.of_isConj hx hw
  tableVII := h.tableVII.of_isConj hx hw
  lines := h.lines.of_isConj hx hw
  oddInv := h.oddInv.of_isConj hx hw
  gamma := h.gamma.of_isConj hx hw
  five := h.five.of_isConj hx hw
  order := h.order

end CFSG.EvenSporadicStandard.HNRecog.Section3
