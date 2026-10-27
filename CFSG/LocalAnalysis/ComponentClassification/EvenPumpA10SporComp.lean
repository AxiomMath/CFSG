module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpA10Comps
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.LocalAnalysis.ComponentClassification.SuzOutComp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.Sporadic.Co2Schreier.ModelSimple
public import CFSG.Sporadic.Schreier.LyOddCoreFree
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial
public import CFSG.Sporadic.SmallOddCore.Co3Catalogue
public import CFSG.Sporadic.ThSchreier.NodeGFExclusion

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint

theorem a10SporClause_McL :
    A10SporClauseFor .McL :=
  a10SporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_McL
    (fun G _ _ _ _ ⟨e⟩ t ht => (RestrictedStd.Spor.mcl_inner_comps e t ht).mono fun Y _ h => by
      obtain ⟨θ⟩ := h
      unfold CompNotA10
      rw [Nat.card_congr θ.toEquiv, Sporadic.SmallOddCore.card_mclX]
      decide)
    (fun G _ _ _ _ ⟨e⟩ α hα2 hα => (RestrictedStd.Spor.mcl_outer_comps e α hα2 hα).mono
      fun Y _ h => by
        unfold CompNotA10
        intro hc
        rw [hc] at h
        norm_num at h)

theorem a10SporClause_Co1 :
    A10SporClauseFor .Co1 :=
  a10SporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_Co1
    (fun G _ _ _ _ ⟨e⟩ t ht B hB => by
      unfold CompNotA10
      rw [(RestrictedStd.Spor.co1LocalComponentsInput_holds G e t ht B hB).1]
      decide)
    (outer_compNotA10_of_forall_inner fun α => by
      obtain ⟨g, hg⟩ := Sporadic.Co1Schreier.full_automorphisms_inner_of_inputs
          Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner α
      exact ⟨g, hg.symm⟩)

theorem a10SporClause_Co2 :
    A10SporClauseFor .Co2 :=
  a10SporClauseFor_of_comps Sporadic.Co2Schreier.sporadicOddCoreFree_Co2
    (fun _ _ _ _ _ ⟨e⟩ t ht B hB =>
      absurd hB (Sporadic.Co2Schreier.CTI_Co2_involution_centralizers_have_no_components e t ht B))
    (outer_compNotA10_of_forall_inner (RestrictedStd.Spor.mem_inner_of_mulEquiv
      Sporadic.Co2Cert.co2PermEquiv Sporadic.Co2Schreier.CTUC_Co2_full_automorphisms_inner))

theorem a10SporClause_Co3 :
    A10SporClauseFor .Co3 :=
  a10SporClauseFor_of_comps Sporadic.SmallOddCore.sporadicOddCoreFree_Co3
    (fun G _ _ _ _ ⟨e⟩ t ht => (RestrictedStd.Spor.co3_inner_comps e t ht).mono fun Y _ h => by
      unfold CompNotA10
      intro hc
      rw [hc] at h
      rcases h with h | h <;> norm_num at h)
    (outer_compNotA10_of_forall_inner fun α => by
      obtain ⟨g, hg⟩ := Sporadic.SmallOddCore.ctuc_co3_all_automorphisms_inner.{0}.2.1.1 α
      exact ⟨g, hg.symm⟩)

theorem a10SporClause_Suz :
    A10SporClauseFor .Suz :=
  a10SporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_Suz
    (fun _ _ _ _ _ ⟨e⟩ t ht B hB => by
      unfold CompNotA10
      rw [Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e t ht B
        hB]
      decide)
    (fun G _ _ _ _ hG α hα2 hα B hB => by
      unfold CompNotA10
      rcases SolMax.suzOuterComponentsInput_holds G hG α hα2 hα B hB with h | h <;> rw [h] <;>
        decide)

theorem a10SporClause_Ly :
    A10SporClauseFor .Ly :=
  a10SporClauseFor_of_comps Sporadic.LySchreier.sporadicOddCoreFree_Ly
    (fun G _ _ _ _ hG t ht B hB => by
      obtain ⟨hq, -, ⟨θ⟩⟩ := Sporadic.LySchreier.involution_centralizers_quasisimple hG t ht
      have hBt := RestrictedStd.Spor.eq_top_of_isComponent_of_isQuasisimple hq hB
      let φ : ↥B ≃* ↥(centralizer ({t} : Set G)) :=
        (MulEquiv.subgroupCongr hBt).trans Subgroup.topEquiv
      unfold CompNotA10
      rw [Nat.card_congr (QuotientGroup.congr (center B) (center _) φ
        (Subgroup.map_center_eq φ)).toEquiv, Nat.card_congr θ.toEquiv,
        SolMax.card_of_mulEquiv_alt (by norm_num) (MulEquiv.refl _)]
      decide)
    (outer_compNotA10_of_forall_inner fun α => by
      have h : OuterAutomorphisms.inner (NativeSporadic.Carrier .Ly) = ⊤ :=
        RestrictedStd.Spor.lyOuterTrivialInput
      rw [h]
      trivial)

theorem a10SporClause_Th :
    A10SporClauseFor .Th :=
  a10SporClauseFor_of_comps Sporadic.ThSchreier.sporadicOddCoreFree_Th
    (fun G _ _ _ _ hG t ht => RestrictedStd.Spor.compsSatisfy_of_charP
      ((Sporadic.ThSchreier.ctuc_Th_inner_involution_centralizers_characteristic_two.2.2 G
        hG).1 t ht).1 _)
    (outer_compNotA10_of_forall_inner fun α => by
      have h : OuterAutomorphisms.inner (NativeSporadic.Carrier .Th) = ⊤ :=
        Sporadic.ThSchreier.inner_Th
      rw [h]
      trivial)

end CFSG.ComponentClassification.EvenPump
