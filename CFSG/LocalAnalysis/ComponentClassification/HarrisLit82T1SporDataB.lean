module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.Sporadic.SuzOddCore.CTIComponents
public import CFSG.Sporadic.ONOddCore.ONan
public import CFSG.Sporadic.ONOddCore.LocalComp
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.Sporadic.Co2Schreier.ModelSimple
public import CFSG.Sporadic.SmallOddCore.Co3Catalogue
public import CFSG.Sporadic.HNOddCore.HN
public import CFSG.Sporadic.Schreier.LyOddCoreFree
public import CFSG.Sporadic.ThSchreier.NodeGFExclusion
public import CFSG.Sporadic.Schreier.J4SCatalogU
public import CFSG.Sporadic.Schreier.J4SNoComp
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1SporLie

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.SporRow

open CFSG Subgroup CFSG.Blueprint

theorem sporT1Data_Suz
    : SporT1Data .Suz where
  oddCore := oddCore_of_free CatalogueU.sporadicOddCoreFree_Suz
  comps := fun _ _ _ _ _ e t ht B hB _ => by
    rw [Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e t ht B hB]
    exact fun h => not_oddLieOrder_L34 h.oddLieOrder

theorem sporT1Data_ONan
    : SporT1Data .ONan where
  oddCore := oddCore_of_free Sporadic.ONOddCore.sporadicOddCoreFree_ONan
  comps := fun _ _ _ _ _ e t ht B hB _ => by
    rw [Sporadic.ONOddCore.cti_on_involution_local_components_projective_linear_quotient_order
      ⟨e⟩ t ht B hB]
    exact fun h => not_oddLieOrder_L34 h.oddLieOrder

theorem sporT1Data_Co1
    : SporT1Data .Co1 where
  oddCore := oddCore_of_free CatalogueU.sporadicOddCoreFree_Co1
  comps := fun S _ _ _ _ e t ht B hB _ => by
    rw [(RestrictedStd.Spor.co1LocalComponentsInput_holds S e t ht B hB).1]
    exact fun h => not_oddLieOrder_G24 h.oddLieOrder

theorem sporT1Data_Co2
    : SporT1Data .Co2 where
  oddCore := oddCore_of_free Sporadic.Co2Schreier.sporadicOddCoreFree_Co2
  comps := fun _ _ _ _ _ e t ht B hB _ =>
    absurd hB (Sporadic.Co2Schreier.CTI_Co2_involution_centralizers_have_no_components e t ht B)

theorem sporT1Data_Co3
    : SporT1Data .Co3 where
  oddCore := oddCore_of_free Sporadic.SmallOddCore.sporadicOddCoreFree_Co3
  comps := fun _ _ _ _ _ e t ht B hB _ => by
    have h := RestrictedStd.Spor.co3_inner_comps e t ht B hB
    simp only [RestrictedStd.Spor.co3Orders, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h <;> rw [h]
    · exact fun h => not_oddLieOrder_Sp62 h.oddLieOrder
    · exact fun h => not_oddLieOrder_M12 h.oddLieOrder

theorem sporT1Data_Fi22
    : SporT1Data .Fi22 where
  oddCore := oddCore_of_free CatalogueU.sporadicOddCoreFree_Fi22
  comps := fun _ _ _ _ _ e t ht B hB _ => by
    rw [Sporadic.FischerOddCore.CTI_Fi22_involution_local_components_unitary_quotient_order
      e t ht B hB]
    exact fun h => not_oddLieOrder_U62 h.oddLieOrder

theorem sporT1Data_Fi23
    : SporT1Data .Fi23 where
  oddCore := oddCore_of_free CatalogueU.sporadicOddCoreFree_Fi23
  comps := fun _ _ _ _ _ e t ht B hB _ => by
    have h := RestrictedStd.Spor.fi23_inner_comps e t ht B hB
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h <;> rw [h]
    · exact fun h => not_oddLieOrder_Fi22 h.oddLieOrder
    · exact fun h => not_oddLieOrder_U62 h.oddLieOrder

open CFSG.Sporadic.FischerOddCore in
theorem sporT1Data_Fi24Prime
    : SporT1Data .Fi24Prime where
  oddCore := oddCore_of_free CatalogueU.sporadicOddCoreFree_Fi24Prime
  comps := fun _ _ _ _ _ e t ht B hB _ => by
    have h :=
      CTI_Fi24prime_involution_local_components_simple_quotient_divisible_by_eleven e t ht B hB
    rw [h.1]
    exact fun h => not_oddLieOrder_Fi22 h.oddLieOrder

theorem sporT1Data_HN
    : SporT1Data .HN where
  oddCore := oddCore_of_free Sporadic.HNOddCore.sporadicOddCoreFree_HN
  comps := fun S _ _ _ _ e t ht B hB _ => by
    rw [RestrictedStd.Spor.hnLocalComponentsInput_holds S e t ht B hB]
    exact fun h => not_oddLieOrder_HS h.oddLieOrder

theorem sporT1Data_Ly
    : SporT1Data .Ly where
  oddCore := oddCore_of_free Sporadic.LySchreier.sporadicOddCoreFree_Ly
  comps := fun S _ _ _ _ e t ht B hB _ => by
    obtain ⟨hq, -, ⟨eA⟩⟩ := Sporadic.LySchreier.involution_centralizers_quasisimple ⟨e⟩ t ht
    have hcard : Nat.card (centralizer ({t} : Set S) ⧸ center (centralizer ({t} : Set S))) =
        19958400 := by
      rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      norm_num [Nat.factorial]
    have h := RestrictedStd.Spor.compsSatisfy_of_isQuasisimple hq
      (RestrictedStd.Spor.isoInvariant_card_quotient_center {19958400}) hcard B hB
    rw [Set.mem_singleton_iff.1 h]
    exact fun h => not_oddLieOrder_A11 h.oddLieOrder

theorem sporT1Data_Th
    : SporT1Data .Th where
  oddCore := oddCore_of_free Sporadic.ThSchreier.sporadicOddCoreFree_Th
  comps := fun S _ _ _ _ e t ht B hB _ =>
    RestrictedStd.Spor.compsSatisfy_of_charP
      ((Sporadic.ThSchreier.ctuc_Th_inner_involution_centralizers_characteristic_two.2.2 S
        ⟨e⟩).1 t ht).1 (fun Y _ => ¬ IndLieOrder (Nat.card (Y ⧸ center Y))) B hB

theorem sporT1Data_J4
    : SporT1Data .J4 where
  oddCore := oddCore_of_free CatalogueU.sporadicOddCoreFree_J4
  comps := fun S _ _ _ _ e t ht B hB _ =>
    absurd hB (RestrictedStd.Spor.j4NoComponentsInput S ⟨e⟩ t ht B)

end CFSG.ComponentClassification.HarrisLit.T1.SporRow
