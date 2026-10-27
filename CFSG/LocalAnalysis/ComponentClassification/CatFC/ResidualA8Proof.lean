module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.ResidualA8
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.ResidualA8Suz
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.ResidualA8He
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.ResidualA8ON
public import CFSG.LocalAnalysis.ComponentClassification.SuzOutComp
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK3Main
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatSporadicAllData

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem heSuzONNoAltEight_proved : HeSuzONNoAltEight := by
  intro S _ _ hS hna hsp σ hσ D hD hA8
  obtain ⟨φ⟩ := hA8
  have hcard : Nat.card (D ⧸ center D) = 20160 := by
    rw [Nat.card_congr φ.toEquiv]
    exact ResidualA8.card_alt_eight
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  by_cases hin : σ ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨u, rfl⟩ := hin
    have hu : orderOf u = 2 := SeitzReduction.OmegaPilot.orderOf_eq_two_of_conj hS hna hσ
    have hfix : ResidualA8.NoAltEightComponent (fixedSubgroup (MulAut.conj u)) := by
      rcases hsp with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
      · exact ResidualA8.noAltEightComponent_he_fixed e hu
      · exact ResidualA8.NoAltEightComponent.of_mulEquiv (MulEquiv.subgroupCongr
          (SeitzReduction.SporadicRefine.fixedSubgroup_conj_eq_centralizerOf u))
          (ResidualA8.noAltEightComponent_suz_centralizer e u hu)
      · exact ResidualA8.NoAltEightComponent.of_mulEquiv (MulEquiv.subgroupCongr
          (SeitzReduction.SporadicRefine.fixedSubgroup_conj_eq_centralizerOf u))
          (ResidualA8.noAltEightComponent_on_centralizer ⟨e⟩ u hu)
    exact hfix D hD ⟨φ⟩
  · rcases hsp with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have h := SeitzReduction.SporadicRefine.card_quotient_center_dvd_card_fixedSubgroup D
      rw [hcard, SeitzReduction.SporadicRefine.he_outer_card_fixedSubgroup e hσ hin] at h
      norm_num at h
    · obtain ⟨B, hB, hBcard⟩ := SeitzReduction.OmegaPilot.exists_component_fixSub σ hD
      have h := SolMax.suzOuterComponentsInput_holds S ⟨e⟩ σ hσ2 hin B hB
      rw [hBcard, hcard] at h
      norm_num at h
    · obtain ⟨B, hB, hBcard⟩ := SeitzReduction.OmegaPilot.exists_component_fixSub σ hD
      have h := SolMax.onOuterComponentsInput_of_local SolMax.ONOut.onOuterLocalInput_holds S ⟨e⟩
        σ hσ2 hin B hB
      rw [hBcard, hcard] at h
      norm_num at h

end CFSG.ComponentClassification.CatFC
