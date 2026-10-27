module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Orders
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVRows
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVOrbit2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVOrbit4A
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVOrbit4B6A
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVCover

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem tableV_of_hyps (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hF2 : Vert Fusion2Facts a z)
    (hF3 : Vert Fusion3Facts a z) (hT3 : Vert TableIIIFacts a z) (hT4 : Vert TableIVFacts a z) :
    TableVFacts a z := by
  have hF1a : Fusion1Facts a z := hF1.self
  have hF2a : Fusion2Facts a z := hF2.self
  have hF3a : Fusion3Facts a z := hF3.self
  have hT4a : TableIVFacts a z := hT4.self
  refine ⟨⟨tableV_subset h, fun c hc => tableV_cover hI h hF1 hF2 hT3 hT4 hc,
    tableV_disjoint hI h, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact tableV_orbit_2A hI h hF1a hF2a
    · exact tableV_orbit_2B hI h hF1a hF2a
    · exact tableV_orbit_4A hI h hF1 hF2 hT3
    · exact tableV_orbit_4B hI h hF1a hF2a hT4a
    · exact tableV_orbit_6A hI h hF1a hF2a hT4a
  · intro i c hc
    rw [← Gxy_eq_inf]
    fin_cases i
    · exact card_of_isShapeTwoTwoTimesA8 (hF3a.shape_2A c hc)
    · exact card_of_isShapeTwoTwoSixS5 (hF3a.shape_2B c hc)
    · exact perp_card_of_shape (perp_shape_of_mem_orb4A hI h hF1 hT3 hc)
    · exact tableV_card_4B h hT4a hc
    · exact tableV_card_6A h hT4a hc
  · exact fun c hc => hF3a.shape_2A c hc
  · exact fun c hc => hF3a.shape_2B c hc
  · exact fun c hc => perp_shape_of_mem_orb4A hI h hF1 hT3 hc
  · exact fun c hc => tableV_shape_4B h hT4a hc
  · exact fun c hc => tableV_shape_6A h hT4a hc

end CFSG.EvenSporadicStandard.HNRecog.Section3
