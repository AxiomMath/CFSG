module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.CubeTransitive

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem a8Pictures_of_fusion3 (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hCube : Vert CubeFacts a z)
    (hA8 : Vert A8Shapes a z) (hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z) :
    A8Pictures a z where
  fig8a := fig8a_of_fusion2 hI h hF1 hF2 hA8.self
  fig8b := fig8b_of_fusion2 hI h hF1 hF2 hA8.self
  cube_conj := cube_conj_of_fusion3 hF3.self
  cube_transitive := cube_transitive_of_fusion3 hI h hF1 hF2 hF3 hA8

end CFSG.EvenSporadicStandard.HNRecog.Section3
