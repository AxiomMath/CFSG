module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Model
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Out
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpInputs
public import CFSG.Sporadic.ONOddCore.LocalComp

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup


theorem on_of (hOut : SolMax.ONOuterComponentsInput) :
    CF23InnerFusionFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .ONan := by
  intro G _ _ N hN hC hY α J hα hJN hJα hJ _ hsmall _ _
  obtain ⟨e⟩ := hY
  have := hN
  have e' : ↥N ≃* Blueprint.NativeSporadic.ON := e
  exfalso
  by_cases hαN : α ∈ N
  · exact false_of_inner_card' hα hαN hJN hJα hJ hsmall fun a ha B hB =>
      Sporadic.ONOddCore.cti_on_involution_local_components_projective_linear_quotient_order
        ⟨e'⟩ a ha B hB
  · obtain ⟨h2, hout⟩ := conjNormal_outer hC hα hαN
    obtain ⟨hle, hcomp⟩ := isComponent_fixSub hJN hJα hJ
    have hcard := hOut ↥N ⟨e'⟩ _ h2 hout _ hcomp
    exact not_small_of_card_ne (Or.inr (Or.inl ((card_quotient_center_congr
      ((subgroupOfEquivOfLe hle).trans (subgroupOfEquivOfLe hJN))).symm.trans hcard))) hsmall

end CFSG.ComponentClassification.GSThmB.CF23I
