module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22
public import CFSG.Sporadic.HNOddCore.HN
public import CFSG.Sporadic.HNOddCore.OuterFix

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.Blueprint
open CFSG.Sporadic.FischerOddCore
  (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven)

theorem altPumpSpor_Fi22 :
    AltPumpSporClauseFor .Fi22 :=
  altPumpSporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_Fi22
    (fun _ _ _ _ _ ⟨e⟩ t ht B hB => noOddAltBelow_of_card_quotient_center_eq (c := 9196830720)
      (factorial_div_two_ne 14 (by decide) (by decide))
      (Sporadic.FischerOddCore.CTI_Fi22_involution_local_components_unitary_quotient_order e t ht
        B hB))
    (fun G _ _ _ _ hG α hα2 hα B hB => by
      rcases Sporadic.FischerOddCore.fi22OuterComponentsInput_holds G hG α hα2 hα B hB with h | h
      · exact noOddAltBelow_of_card_quotient_center_eq (c := 174182400)
          (factorial_div_two_ne 12 (by decide) (by decide)) h
      · exact noOddAltBelow_of_card_quotient_center_eq (c := 1451520)
          (factorial_div_two_ne 10 (by decide) (by decide)) h)

theorem altPumpSpor_Fi23 :
    AltPumpSporClauseFor .Fi23 :=
  altPumpSporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_Fi23
    (fun G _ _ _ _ ⟨e⟩ t ht => (RestrictedStd.Spor.fi23_inner_comps e t ht).mono fun Y _ h => by
      rcases h with h | h
      · exact noOddAltBelow_of_card_quotient_center_eq (c := 64561751654400)
          (factorial_div_two_ne 17 (by decide) (by decide)) h
      · exact noOddAltBelow_of_card_quotient_center_eq (c := 9196830720)
          (factorial_div_two_ne 14 (by decide) (by decide)) (Set.mem_singleton_iff.1 h))
    (outer_noOddAlt_of_forall_inner fun α => by
      obtain ⟨g, hg⟩ := Sporadic.FischerOddCore.CTUC_Fi23_Schreier.2.1 α
      exact ⟨g, hg.symm⟩)

theorem altPumpSpor_Fi24Prime :
    AltPumpSporClauseFor .Fi24Prime :=
  altPumpSporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_Fi24Prime
    (fun _ _ _ _ _ ⟨e⟩ t ht B hB => noOddAltBelow_of_card_quotient_center_eq
      (c := 64561751654400) (factorial_div_two_ne 17 (by decide) (by decide))
      (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven e t ht B
        hB).1)
    (fun G _ _ _ _ hG α hα2 hα B hB => by
      rcases Sporadic.FischerOddCore.fi24primeOuterComponentsInput_holds G hG α hα2 hα B hB with
        h | h
      · exact noOddAltBelow_of_card_quotient_center_eq (c := 4089470473293004800)
          (factorial_div_two_ne 21 (by decide) (by decide)) h
      · exact noOddAltBelow_of_card_quotient_center_eq (c := 9196830720)
          (factorial_div_two_ne 14 (by decide) (by decide)) h)

theorem altPumpSpor_HN :
    AltPumpSporClauseFor .HN :=
  altPumpSporClauseFor_of_comps Sporadic.HNOddCore.sporadicOddCoreFree_HN
    (fun G _ _ _ _ ⟨e⟩ t ht B hB => noOddAltBelow_of_card_quotient_center_eq (c := 44352000)
      (factorial_div_two_ne 12 (by decide) (by decide))
      (RestrictedStd.Spor.hnLocalComponentsInput_holds G e t ht B hB))
    (fun G _ _ _ _ ⟨e⟩ α hα2 hα => by
      have h1 : α ≠ 1 := by
        rintro rfl
        exact hα ⟨1, map_one _⟩
      obtain ⟨θ⟩ := Sporadic.HNOddCore.hn_outer_involution_fixSub e α
        (orderOf_eq_prime (by rw [sq]; exact hα2) h1) hα
      exact RestrictedStd.Spor.CompsSatisfy.of_mulEquiv (isoInvariant_noOddAltBelow _) θ
        (RestrictedStd.Spor.compsSatisfy_perm_ten.mono fun Y _ h =>
          noOddAltBelow_of_card_quotient_center_eq (c := 1814400)
            (factorial_div_two_ne 11 (by decide) (by decide)) (Set.mem_singleton_iff.1 h)))

end CFSG.ComponentClassification.SolMax
