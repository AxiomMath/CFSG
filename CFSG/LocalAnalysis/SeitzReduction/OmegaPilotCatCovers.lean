module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatStatement
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatCovers

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centerQuotientAut FixedCentralizerTwoFree centerFixedProjection
  orderOf_centerQuotientAut centerQuotientAut_mem_range odd_card_center_of_twoFree
  twoFree_centerQuotientAut)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall isComponent_map_centerFixedProjection
  odd_card_center_of_twoSmall_inner twoSmall_centerQuotientAut)

theorem catOmegaCovers : CatOmegaCovers := by
  intro K _ _ hK τ hτ t m f D hD hDm
  have : Group.IsPerfect K := hK.1
  obtain ⟨hD', ⟨e⟩⟩ := isComponent_map_centerFixedProjection hD
  refine ⟨orderOf_centerQuotientAut hτ, centerQuotientAut_mem_range,
    D.map (centerFixedProjection τ), hD', LieType.CurtisTits.lieModel_of_mulEquiv e hDm,
    UnitaryPilot.odd_card_center_map_centerFixedProjection hD,
    fun hodd => ⟨odd_card_center_of_twoFree hτ hodd, twoFree_centerQuotientAut hD hτ hodd⟩,
    fun hin hsmall => ?_⟩
  have hZ := odd_card_center_of_twoSmall_inner hτ hin hsmall
  exact ⟨hZ, twoSmall_centerQuotientAut hD hZ hsmall⟩

end CFSG.SeitzReduction.OmegaPilot
