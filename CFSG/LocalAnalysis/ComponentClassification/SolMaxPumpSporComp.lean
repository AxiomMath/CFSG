module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.FourExactOuter
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.Sporadic.Co2Schreier.ModelSimple
public import CFSG.Sporadic.Schreier.J4SCatalogU
public import CFSG.Sporadic.Schreier.J4SNoComp
public import CFSG.Sporadic.Schreier.LyOddCoreFree
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial
public import CFSG.Sporadic.SmallOddCore.Co3Catalogue
public import CFSG.Sporadic.ThSchreier.NodeGFExclusion

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.Blueprint

theorem altPumpSpor_McL :
    AltPumpSporClauseFor .McL :=
  altPumpSporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_McL
    (fun G _ _ _ _ ⟨e⟩ t ht => (RestrictedStd.Spor.mcl_inner_comps e t ht).mono fun Y _ h => by
      obtain ⟨θ⟩ := h
      exact noOddAltBelow_of_card_quotient_center_eq (c := 20160)
        (factorial_div_two_ne 9 (by decide) (by decide))
        (by rw [Nat.card_congr θ.toEquiv, Sporadic.SmallOddCore.card_mclX]))
    (fun G _ _ _ _ ⟨e⟩ α hα2 hα => (RestrictedStd.Spor.mcl_outer_comps e α hα2 hα).mono
      fun Y _ h => noOddAltBelow_of_card_quotient_center_eq (c := 7920)
        (factorial_div_two_ne 8 (by decide) (by decide)) (Set.mem_singleton_iff.1 h))

theorem altPumpSpor_Co1 :
    AltPumpSporClauseFor .Co1 :=
  altPumpSporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_Co1
    (fun G _ _ _ _ ⟨e⟩ t ht B hB => noOddAltBelow_of_card_quotient_center_eq (c := 251596800)
      (factorial_div_two_ne 13 (by decide) (by decide))
      (RestrictedStd.Spor.co1LocalComponentsInput_holds G e t ht B hB).1)
    (outer_noOddAlt_of_forall_inner fun α => by
      obtain ⟨g, hg⟩ := Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
          Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner α
      exact ⟨g, hg.symm⟩)

theorem altPumpSpor_Co2 :
    AltPumpSporClauseFor .Co2 :=
  altPumpSporClauseFor_of_comps Sporadic.Co2Schreier.sporadicOddCoreFree_Co2
    (fun _ _ _ _ _ ⟨e⟩ t ht B hB =>
      absurd hB (Sporadic.Co2Schreier.CTI_Co2_involution_centralizers_have_no_components e t ht B))
    (outer_noOddAlt_of_forall_inner (RestrictedStd.Spor.mem_inner_of_mulEquiv
      Sporadic.Co2Cert.co2PermEquiv Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner))

theorem altPumpSpor_Co3 :
    AltPumpSporClauseFor .Co3 :=
  altPumpSporClauseFor_of_comps Sporadic.SmallOddCore.sporadicOddCoreFree_Co3
    (fun G _ _ _ _ ⟨e⟩ t ht => (RestrictedStd.Spor.co3_inner_comps e t ht).mono fun Y _ h => by
      rcases h with h | h
      · exact noOddAltBelow_of_card_quotient_center_eq (c := 1451520)
          (factorial_div_two_ne 10 (by decide) (by decide)) h
      · exact noOddAltBelow_of_card_quotient_center_eq (c := 95040)
          (factorial_div_two_ne 9 (by decide) (by decide)) h)
    (outer_noOddAlt_of_forall_inner fun α => by
      obtain ⟨g, hg⟩ := Sporadic.SmallOddCore.ctuc_co3_all_automorphisms_inner.{0}.2.1.1 α
      exact ⟨g, hg.symm⟩)

theorem altPumpSpor_Ly :
    AltPumpSporClauseFor .Ly :=
  altPumpSporClauseFor_of_comps Sporadic.LySchreier.sporadicOddCoreFree_Ly
    (fun G _ _ _ _ hG t ht => by
      obtain ⟨hq, hZ, -⟩ := Sporadic.LySchreier.involution_centralizers_quasisimple hG t ht
      refine compsSatisfy_noOddAltBelow_of_quasisimple hq fun h => ?_
      rw [h, Subgroup.card_bot] at hZ
      omega)
    (outer_noOddAlt_of_forall_inner fun α => by
      have h : OuterAutomorphisms.inner (NativeSporadic.Carrier .Ly) = ⊤ :=
        RestrictedStd.Spor.lyOuterTrivialInput
      rw [h]
      trivial)

theorem altPumpSpor_Th :
    AltPumpSporClauseFor .Th :=
  altPumpSporClauseFor_of_comps Sporadic.ThSchreier.sporadicOddCoreFree_Th
    (fun G _ _ _ _ hG t ht => RestrictedStd.Spor.compsSatisfy_of_charP
      ((Sporadic.ThSchreier.ctuc_Th_inner_involution_centralizers_characteristic_two.2.2 G
        hG).1 t ht).1 _)
    (outer_noOddAlt_of_forall_inner fun α => by
      have h : OuterAutomorphisms.inner (NativeSporadic.Carrier .Th) = ⊤ :=
        Sporadic.ThSchreier.inner_Th
      rw [h]
      trivial)

theorem altPumpSpor_J4 :
    AltPumpSporClauseFor .J4 :=
  altPumpSporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_J4
    (fun G _ _ _ _ hG t ht B hB =>
      absurd hB (RestrictedStd.Spor.j4NoComponentsInput G hG t ht B))
    (fun G _ _ _ _ ⟨e⟩ α hα2 hα => by
      by_cases h1 : α = 1
      · exact absurd ⟨1, by rw [h1, map_one]⟩ hα
      · exact absurd (RestrictedStd.Spor.mem_inner_of_J4 e α
          (orderOf_eq_prime (by rw [sq]; exact hα2) h1)) hα)

end CFSG.ComponentClassification.SolMax
