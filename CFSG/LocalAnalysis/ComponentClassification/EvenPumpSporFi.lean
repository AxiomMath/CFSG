module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseFi23
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSporBasic

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG.ComponentClassification.SolMax
open CFSG Subgroup CFSG.Blueprint
open CFSG.Sporadic.FischerOddCore
  (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven)

theorem evenPumpSpor_Fi22 :
    EvenPumpSporClauseFor .Fi22 :=
  evenPumpSporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_Fi22
    (fun _ _ _ _ _ ⟨e⟩ t ht B hB => noEvenAltBelow_of_card_quotient_center_eq (c := 9196830720)
      (factorial_div_two_ne_even 14 (by decide) (by decide))
      (Sporadic.FischerOddCore.CTI_Fi22_involution_local_components_unitary_quotient_order e t ht
        B hB))
    (fun G _ _ _ _ hG α hα2 hα B hB => by
      rcases Sporadic.FischerOddCore.fi22OuterComponentsInput_holds G hG α hα2 hα B hB with h | h
      · exact noEvenAltBelow_of_card_quotient_center_eq (c := 174182400)
          (factorial_div_two_ne_even 12 (by decide) (by decide)) h
      · exact noEvenAltBelow_of_card_quotient_center_eq (c := 1451520)
          (factorial_div_two_ne_even 10 (by decide) (by decide)) h)

theorem evenPumpSpor_Fi23 :
    EvenPumpSporClauseFor .Fi23 :=
  evenPumpSporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_Fi23
    (fun G _ _ _ _ ⟨e⟩ t ht => (RestrictedStd.Spor.fi23_inner_comps e t ht).mono fun Y _ h => by
      rcases h with h | h
      · exact noEvenAltBelow_of_card_quotient_center_eq (c := 64561751654400)
          (factorial_div_two_ne_even 17 (by decide) (by decide)) h
      · exact noEvenAltBelow_of_card_quotient_center_eq (c := 9196830720)
          (factorial_div_two_ne_even 14 (by decide) (by decide)) (Set.mem_singleton_iff.1 h))
    (outer_noEvenAlt_of_forall_inner fun α => by
      obtain ⟨g, hg⟩ := Sporadic.FischerOddCore.CTUC_Fi23_Schreier.2.1 α
      exact ⟨g, hg.symm⟩)

theorem evenPumpSpor_Fi24Prime :
    EvenPumpSporClauseFor .Fi24Prime :=
  evenPumpSporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_Fi24Prime
    (fun _ _ _ _ _ ⟨e⟩ t ht B hB => noEvenAltBelow_of_card_quotient_center_eq
      (c := 64561751654400) (factorial_div_two_ne_even 17 (by decide) (by decide))
      (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven e t ht B
        hB).1)
    (fun G _ _ _ _ hG α hα2 hα B hB => by
      rcases Sporadic.FischerOddCore.fi24primeOuterComponentsInput_holds G hG α hα2 hα B hB with
        h | h
      · exact noEvenAltBelow_of_card_quotient_center_eq (c := 4089470473293004800)
          (factorial_div_two_ne_even 21 (by decide) (by decide)) h
      · exact noEvenAltBelow_of_card_quotient_center_eq (c := 9196830720)
          (factorial_div_two_ne_even 14 (by decide) (by decide)) h)

end CFSG.ComponentClassification.EvenPump
