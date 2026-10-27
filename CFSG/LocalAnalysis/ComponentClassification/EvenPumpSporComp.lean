module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.Sporadic.Co2Schreier.ModelSimple
public import CFSG.Sporadic.SmallOddCore.Co3Catalogue
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSporBasic

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG.ComponentClassification.SolMax
open CFSG Subgroup CFSG.Blueprint

theorem evenPumpSpor_McL :
    EvenPumpSporClauseFor .McL :=
  evenPumpSporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_McL
    (fun G _ _ _ _ ⟨e⟩ t ht => (RestrictedStd.Spor.mcl_inner_comps e t ht).mono fun Y _ h => by
      obtain ⟨θ⟩ := h
      exact noEvenAltBelow_of_card_quotient_center_eq (c := 20160)
        (factorial_div_two_ne_even 9 (by decide) (by decide))
        (by rw [Nat.card_congr θ.toEquiv, Sporadic.SmallOddCore.card_mclX]))
    (fun G _ _ _ _ ⟨e⟩ α hα2 hα => (RestrictedStd.Spor.mcl_outer_comps e α hα2 hα).mono
      fun Y _ h => noEvenAltBelow_of_card_quotient_center_eq (c := 7920)
        (factorial_div_two_ne_even 8 (by decide) (by decide)) (Set.mem_singleton_iff.1 h))

theorem evenPumpSpor_Co1 :
    EvenPumpSporClauseFor .Co1 :=
  evenPumpSporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_Co1
    (fun G _ _ _ _ ⟨e⟩ t ht B hB => noEvenAltBelow_of_card_quotient_center_eq (c := 251596800)
      (factorial_div_two_ne_even 13 (by decide) (by decide))
      (RestrictedStd.Spor.co1LocalComponentsInput_holds G e t ht B hB).1)
    (outer_noEvenAlt_of_forall_inner fun α => by
      obtain ⟨g, hg⟩ := Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
          Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner α
      exact ⟨g, hg.symm⟩)

theorem evenPumpSpor_Co2 :
    EvenPumpSporClauseFor .Co2 :=
  evenPumpSporClauseFor_of_comps Sporadic.Co2Schreier.sporadicOddCoreFree_Co2
    (fun _ _ _ _ _ ⟨e⟩ t ht B hB =>
      absurd hB (Sporadic.Co2Schreier.CTI_Co2_involution_centralizers_have_no_components e t ht B))
    (outer_noEvenAlt_of_forall_inner (RestrictedStd.Spor.mem_inner_of_mulEquiv
      Sporadic.Co2Cert.co2PermEquiv Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner))

theorem evenPumpSpor_Co3 :
    EvenPumpSporClauseFor .Co3 :=
  evenPumpSporClauseFor_of_comps Sporadic.SmallOddCore.sporadicOddCoreFree_Co3
    (fun G _ _ _ _ ⟨e⟩ t ht => (RestrictedStd.Spor.co3_inner_comps e t ht).mono fun Y _ h => by
      rcases h with h | h
      · exact noEvenAltBelow_of_card_quotient_center_eq (c := 1451520)
          (factorial_div_two_ne_even 10 (by decide) (by decide)) h
      · exact noEvenAltBelow_of_card_quotient_center_eq (c := 95040)
          (factorial_div_two_ne_even 9 (by decide) (by decide)) h)
    (outer_noEvenAlt_of_forall_inner fun α => by
      obtain ⟨g, hg⟩ := Sporadic.SmallOddCore.ctuc_co3_all_automorphisms_inner.{0}.2.1.1 α
      exact ⟨g, hg.symm⟩)

end CFSG.ComponentClassification.EvenPump
