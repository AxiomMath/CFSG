module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Segev
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSide

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem haradaHNRecognitionKP_of_halves (hHarada : HaradaHalf) (hSegev : SegevUniqueness)
    (hHN : HNSideFacts) : TwoHS.HaradaHNRecognitionKP := by
  intro z₀ hz₀ hK G _ _ _ hKP z hz hc
  obtain ⟨E, hE⟩ := exists_isF5Centralizer_of_nonempty_mulEquiv hc
    (hHN.isF5Centralizer_of_component z₀ hz₀ hK)
  obtain ⟨z', hz', hQ⟩ := hHarada G hKP z hz E hE
  obtain ⟨a, b, hab⟩ := hHN.isF5Type
  haveI := hHN.finite
  haveI := hHN.isSimpleGroup
  exact hSegev G (Carrier .HN) z z' a b ⟨hz, hz', ⟨_, hE⟩, hQ⟩ hab

end CFSG.EvenSporadicStandard.HNRecog
