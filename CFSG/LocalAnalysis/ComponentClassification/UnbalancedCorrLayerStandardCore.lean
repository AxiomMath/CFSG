module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup CFSG.LocalAnalysis.ComponentInitial

@[expose] def EscapingOvergroupNotCatalog : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (J : Subgroup G), CFSG.Assembly.IsQuasisimple J →
    Even (Nat.card J) →
    (∃ V : Subgroup G, V ≤ J ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4) →
    IsUniversalComponent J → (block J).Nontrivial → ∀ L : Subgroup G,
    CFSG.Assembly.IsQuasisimple L → blockGroup J ≤ L →
    ¬ L ≤ normalizer (blockGroup J : Set G) → ¬ Blueprint.Catalog (L ⧸ center L)

theorem isStandardSubgroup_of_assembly_isStandardSubgroup {Y : Type*} [Group Y]
    {L : Subgroup Y} (h : Assembly.ComponentType.IsStandardSubgroup L) :
    IsStandardSubgroup L :=
  StandardSubgroupAPI.isStandardSubgroup_iff_assembly.2 h

theorem layer_le_map_layer_top {F : Type*} [Group F] :
    layer F ≤ (layer ↥(⊤ : Subgroup F)).map (⊤ : Subgroup F).subtype := by
  show sSup _ ≤ _
  refine sSup_le fun C hC => ?_
  have h1 := LocalCores.isComponent_map_mulEquiv
    (Subgroup.topEquiv.symm : F ≃* ↥(⊤ : Subgroup F)) hC
  have h2 := LocalCores.component_le_layer h1
  intro x hx
  exact ⟨Subgroup.topEquiv.symm x, h2 ⟨x, hx, rfl⟩, rfl⟩

theorem isComponent_of_isComponentOf_top {F : Type*} [Group F] {L : Subgroup F}
    (h : CFSG.Assembly.IsComponentOf L ⊤) : IsComponent L := by
  have h1 := (isComponentOf_iff_isComponent_subgroupOf le_top).mp h
  have h2 := LocalCores.isComponent_map_mulEquiv
    (Subgroup.topEquiv : ↥(⊤ : Subgroup F) ≃* F) h1
  have h3 : (L.subgroupOf ⊤).map (Subgroup.topEquiv : ↥(⊤ : Subgroup F) ≃* F).toMonoidHom = L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, mem_top x⟩, hx, rfl⟩
  rwa [h3] at h2

theorem layerGeneratedUniversalComponentStandard_of_escapingOvergroupNotCatalog
    (hexcl : EscapingOvergroupNotCatalog) : LayerGeneratedUniversalComponentStandard := by
  intro F _ _ hKF L hLE hLq hV a haC ha2 hcomp hWa
  classical
  have hLqA : CFSG.Assembly.IsQuasisimple L :=
    (AssemblyBPredicates.isQuasisimple_iff_native _).mpr hLq
  have hLne : L ≠ ⊥ := (nontrivial_iff_ne_bot L).mp (LocalCores.isQuasisimple_nontrivial hLq)
  have hJ : IsUniversalComponent L := by
    intro t ht ht2
    have hLt : L ≤ centralizer ({t} : Set F) := fun x hx =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp ht x hx)
    exact (isComponentOf_iff_isComponent_subgroupOf hLt).mpr (hcomp t ht ht2)
  have hevenL : Even (Nat.card L) := by
    obtain ⟨V, hVL, -, hV4⟩ := hV
    have h := Subgroup.card_dvd_of_le hVL
    rw [hV4] at h
    exact even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 4).trans h)
  have hevenC : Even (Nat.card (centralizer (L : Set F))) := by
    have h2 : orderOf (⟨a, haC⟩ : ↥(centralizer (L : Set F))) = 2 :=
      (orderOf_injective (centralizer (L : Set F)).subtype
        (centralizer (L : Set F)).subtype_injective ⟨a, haC⟩).symm.trans ha2
    have h := orderOf_dvd_natCard (⟨a, haC⟩ : ↥(centralizer (L : Set F)))
    rw [h2] at h
    exact even_iff_two_dvd.mpr h
  have hME : ∀ K ∈ block L, K ≤ layer F := by
    rintro K ⟨⟨g, rfl⟩, -⟩
    have : (layer F).Characteristic := LocalCores.layer_characteristic
    have : (layer F).Normal := inferInstance
    rintro _ ⟨x, hx, rfl⟩
    exact this.conj_mem _ (hLE hx) g
  have hMtop : blockGroup L ≤ (layer ↥(⊤ : Subgroup F)).map (⊤ : Subgroup F).subtype :=
    le_trans (iSup₂_le fun K hK => hME K hK) layer_le_map_layer_top
  have hLg : ∀ g : F, ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
    intro g hg
    by_cases heq : L.map (MulAut.conj g).toMonoidHom = L
    · rw [heq, Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hLqA.1)] at hg
      exact hLne hg
    · have hmem : conjSub g L ∈ block L := ⟨⟨g, rfl⟩, Or.inr hg⟩
      have hΔ : (block L).Nontrivial := ⟨L, mem_block_self, conjSub g L, hmem, fun h => heq h.symm⟩
      have hH : normalizer (blockGroup L : Set F) = ⊤ := by
        by_contra hH
        obtain ⟨K, ⟨hKc, hMK⟩, -, -, -, hKH⟩ :=
          (commuting_block_overgroup_single_component_dichotomy hLqA hevenL hJ hΔ
            (N := ⊤) le_top hMtop).2.2 (lt_top_iff_ne_top.mpr hH)
        have hKq := hKc.2.2
        have : IsSimpleGroup (K ⧸ center K) := hKq.2
        exact hexcl F L hLqA hevenL hV hJ hΔ K hKq hMK hKH
          (SectionRank.catalog_of_isKGroupCat_of_surjective hKF K (QuotientGroup.mk' _)
            (QuotientGroup.mk'_surjective _))
      obtain ⟨-, -, -, -, -, -, -, -, -, hcompN, -⟩ :=
        universal_component_commuting_block_normalizer hLqA hevenL hJ
      have hLtop : CFSG.Assembly.IsComponentOf L ⊤ := hH ▸ hcompN L mem_block_self
      have hNL := LocalCores.layer_le_normalizer (isComponent_of_isComponentOf_top hLtop)
      have hW : (⨆ e ∈ layer F, conjugate L e) = L := by
        refine le_antisymm (iSup₂_le fun e he => ?_) ?_
        · intro y hy
          rw [UnbalancedLayer.mem_conjugate_iff] at hy
          have h1 := (mem_normalizer_iff.mp (inv_mem (hNL he)) (e * y * e⁻¹)).mp hy
          rwa [show e⁻¹ * (e * y * e⁻¹) * e⁻¹⁻¹ = y by group] at h1
        · intro y hy
          refine le_iSup₂ (f := fun e (_ : e ∈ layer F) => conjugate L e) 1 (one_mem _) ?_
          rw [UnbalancedLayer.mem_conjugate_iff]
          simpa using hy
      have hLa : ⁅L, zpowers a⁆ = ⊥ :=
        commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp (zpowers_le.mpr haC))
      rw [hW, hLa] at hWa
      exact hLne hWa.symm
  exact isStandardSubgroup_of_assembly_isStandardSubgroup
    ((involution_component_standard_criterion hLqA hevenC hLg).mpr hJ)

end CFSG.ComponentClassification.UnbalancedCorr
