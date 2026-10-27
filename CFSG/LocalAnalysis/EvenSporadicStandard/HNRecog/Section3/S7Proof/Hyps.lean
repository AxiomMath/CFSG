module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Orbits
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

structure S7Hyps {G : Type} [Group G] (a z : G) : Prop where
  isF5 : IsF5Type a z
  cube : Vert CubeFacts a z
  fusion3 : Vert Fusion3Facts a z
  pic : Vert A8Pictures a z
  parity : Vert ParityFacts a z
  tableIV : Vert TableIVFacts a z
  perp : Vert PerpFacts a z
  tableV : Vert TableVFacts a z

theorem S7Hyps.of_isConj {G : Type} [Group G] {a z x w : G} (H : S7Hyps a z) (hx : IsConj a x)
    (hw : IsConj z w) : S7Hyps x w :=
  ⟨isF5Type_of_isConj H.isF5 hx hw, H.cube.of_isConj hx hw, H.fusion3.of_isConj hx hw,
    H.pic.of_isConj hx hw, H.parity.of_isConj hx hw, H.tableIV.of_isConj hx hw,
    H.perp.of_isConj hx hw, H.tableV.of_isConj hx hw⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
