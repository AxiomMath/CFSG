module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75E8
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75L2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Sec43
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Sec45
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Sec47
public import CFSG.Open.MacWilliamsFourGenerator

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

theorem harada75E8_holds :
    Harada75E8 := by
  unfold Harada75E8
  intro S _ _ hS A hA hA8 hCA U
  suffices hgen : GenLE4 S from hgen U
  by_cases hex : ∃ E : Subgroup S, E.Normal ∧ IsElemAbelian 2 E ∧ Nat.card E = 8
  · obtain ⟨E, hEn, hE, hE8⟩ := hex
    by_cases hAn : A.Normal
    · exact harada_lemma4 hS hA hA8 hCA hAn
    · have hne : A ≠ E := fun h => hAn (h ▸ hEn)
      rcases inter_card_two_or_four hS hA hA8 hCA hE hE8 hEn hne with h2 | h4
      · obtain ⟨F, z, hcfg⟩ := cfg2_of_AE hS hA hA8 hCA hE hE8 hEn h2
        exact genLE4_of_cfg2 hS hcfg
      · by_cases hcfg : ∃ (F : Subgroup S) (z : S), Cfg2 S E F z
        · obtain ⟨F, z, h⟩ := hcfg
          exact genLE4_of_cfg2 hS h
        · have hno : ∀ (F : Subgroup S) (z : S), ¬ Cfg2 S E F z := fun F z h => hcfg ⟨F, z, h⟩
          have := hEn
          exact sec47_final hS hA hA8 hCA hE hE8 h4
            (card_normalizer_le_32 hS hA hA8 hCA hAn hE hE8 hEn h4 hno)
  · exact CFSG.Open.Open.macwilliams_four_generator S hS
      (fun E hEn hE hE8 => hex ⟨E, hEn, hE, hE8⟩)

end CFSG.EvenSporadicStandard.Fin76b
