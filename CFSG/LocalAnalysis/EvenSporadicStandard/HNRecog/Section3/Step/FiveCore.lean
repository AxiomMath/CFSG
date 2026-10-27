module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Cent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.OddCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem fiveCore_of_gamma (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
    (hS7 : Vert S7Facts a z) (hGam : Vert GammaFacts a z) : FiveCoreFacts a z :=
  five_odd_core hI h (five_cent hI h (five_sylow hI h hF1.self hF2.self)) hS7.self hGam.self

end CFSG.EvenSporadicStandard.HNRecog.Section3
