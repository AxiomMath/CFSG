module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.Sporadic.ONOddCore.ONan
public import CFSG.Sporadic.SuzOddCore.CTIComponents

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.Blueprint

theorem altPumpSpor_Suz
    (hSuz : SuzOuterComponentsInput) : AltPumpSporClauseFor .Suz :=
  altPumpSporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_Suz
    (fun _ _ _ _ _ ⟨e⟩ t ht B hB => noOddAltBelow_of_card_quotient_center_eq (c := 20160)
      (factorial_div_two_ne 9 (by decide) (by decide))
      (Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e t ht B hB))
    (fun G _ _ _ _ hG α hα2 hα B hB => by
      rcases hSuz G hG α hα2 hα B hB with h | h
      · exact noOddAltBelow_of_card_quotient_center_eq (c := 95040)
          (factorial_div_two_ne 9 (by decide) (by decide)) h
      · exact noOddAltBelow_of_card_quotient_center_eq (c := 604800)
          (factorial_div_two_ne 10 (by decide) (by decide)) h)

theorem altPumpSpor_ONan
    (hON : ONOuterComponentsInput) : AltPumpSporClauseFor .ONan :=
  altPumpSporClauseFor_of_comps Sporadic.ONOddCore.sporadicOddCoreFree_ONan
    (fun _ _ _ _ _ hG t ht B hB => noOddAltBelow_of_card_quotient_center_eq (c := 20160)
      (factorial_div_two_ne 9 (by decide) (by decide))
      (Sporadic.ONOddCore.cti_on_involution_local_components_projective_linear_quotient_order hG
        t ht B hB))
    (fun G _ _ _ _ hG α hα2 hα B hB => noOddAltBelow_of_card_quotient_center_eq (c := 175560)
      (factorial_div_two_ne 9 (by decide) (by decide)) (hON G hG α hα2 hα B hB))

end CFSG.ComponentClassification.SolMax
