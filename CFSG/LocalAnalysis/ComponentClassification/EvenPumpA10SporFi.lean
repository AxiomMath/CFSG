module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA10Comps
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporCaseFi23
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint
open CFSG.Sporadic.FischerOddCore
  (CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven)

theorem a10SporClause_Fi22 :
    A10SporClauseFor .Fi22 :=
  a10SporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_Fi22
    (fun _ _ _ _ _ ⟨e⟩ t ht B hB => by
      unfold CompNotA10
      rw [Sporadic.FischerOddCore.CTI_Fi22_involution_local_components_unitary_quotient_order e t
        ht B hB]
      decide)
    (fun G _ _ _ _ hG α hα2 hα B hB => by
      unfold CompNotA10
      rcases Sporadic.FischerOddCore.fi22OuterComponentsInput_holds G hG α hα2 hα B hB with
        h | h <;> rw [h] <;> decide)

theorem a10SporClause_Fi23 :
    A10SporClauseFor .Fi23 :=
  a10SporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_Fi23
    (fun G _ _ _ _ ⟨e⟩ t ht => (RestrictedStd.Spor.fi23_inner_comps e t ht).mono fun Y _ h => by
      unfold CompNotA10
      intro hc
      rw [hc] at h
      norm_num at h)
    (outer_compNotA10_of_forall_inner fun α => by
      obtain ⟨g, hg⟩ := Sporadic.FischerOddCore.CTUC_Fi23_Schreier.2.1 α
      exact ⟨g, hg.symm⟩)

theorem a10SporClause_Fi24Prime :
    A10SporClauseFor .Fi24Prime :=
  a10SporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_Fi24Prime
    (fun _ _ _ _ _ ⟨e⟩ t ht B hB => by
      unfold CompNotA10
      rw [(CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven e t ht
        B hB).1]
      decide)
    (fun G _ _ _ _ hG α hα2 hα B hB => by
      unfold CompNotA10
      rcases Sporadic.FischerOddCore.fi24primeOuterComponentsInput_holds G hG α hα2 hα B hB with
        h | h <;> rw [h] <;> decide)

end CFSG.ComponentClassification.EvenPump
