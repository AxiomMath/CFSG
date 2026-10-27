module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Cube.NoCube
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Cube.M11

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem cube_of_fusion1 (hI : TwoHSInterface) (hM : M11Facts) {G : Type} [Group G] [Finite G]
    {a z : G} (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) : CubeFacts a z where
  no_cube := no_cube_of_fusion1 hI h hF1.self
  m11_two_A := m11_two_A_of_fusion1 hI hM h hF1

end CFSG.EvenSporadicStandard.HNRecog.Section3
