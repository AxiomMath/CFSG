module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOneTwo

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G] {H : Subgroup G} {z : G}

theorem class_conj_in_closure [Finite G] (hz : orderOf z = 2)
    (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) (h1 : ProductUniqueContainment H z)
    {T : Set G} (hT : T ⊆ involutionPointClass z) (hzT : z ∈ T) {x' : G} (hx'T : x' ∈ T)
    (hx' : x' • (QuotientGroup.mk 1 : G ⧸ H) ≠ QuotientGroup.mk 1) {t : G} (ht : t ∈ T) :
    ∃ y ∈ Subgroup.closure T, t = y⁻¹ * z * y := by
  have hjoin : ∀ {s₁ s₂ : G}, s₁ ∈ T → s₂ ∈ T →
      Subgroup.closure ({s₁, s₂} : Set G) ≤ Subgroup.closure T :=
    fun h₁ h₂ => Subgroup.closure_mono (by
      rintro x (rfl | rfl)
      · exact h₁
      · exact h₂)
  have hzbase : z • (QuotientGroup.mk 1 : G ⧸ H) = QuotientGroup.mk 1 :=
    (smul_eq_iff_eq_base huniq _).mpr rfl
  have hzcls := distinguished_mem_pointClass z
  by_cases htbase : t • (QuotientGroup.mk 1 : G ⧸ H) = QuotientGroup.mk 1
  · obtain ⟨g, hg, hgx⟩ := conj_in_join_of_fixes_ne hz huniq h1 (hT ht) (hT hx'T) htbase hx'
    obtain ⟨g', hg', hg'x⟩ := conj_in_join_of_fixes_ne hz huniq h1 hzcls (hT hx'T) hzbase hx'
    refine ⟨g' * g⁻¹, Subgroup.mul_mem _ (hjoin hzT hx'T hg')
      (Subgroup.inv_mem _ (hjoin ht hx'T hg)), ?_⟩
    have h : t = g * x' * g⁻¹ := by rw [hgx]; group
    rw [h, hg'x]
    group
  · obtain ⟨g, hg, hgt⟩ := conj_in_join_of_fixes_ne hz huniq h1 hzcls (hT ht) hzbase htbase
    exact ⟨g, hjoin hzT ht hg, hgt⟩

theorem hull_closure_eq_top [Finite G] (hz : orderOf z = 2)
    (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) (h1 : ProductUniqueContainment H z)
    {T : Set G} (hT : T ⊆ involutionPointClass z) (hzT : z ∈ T) {x' : G} (hx'T : x' ∈ T)
    (hx' : x' • (QuotientGroup.mk 1 : G ⧸ H) ≠ QuotientGroup.mk 1) :
    involutionPointHull (⟨z, Subgroup.subset_closure hzT⟩ : Subgroup.closure T) = ⊤ := by
  let Y := Subgroup.closure T
  let zY : Y := ⟨z, Subgroup.subset_closure hzT⟩
  apply Subgroup.map_injective Y.subtype_injective
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  apply le_antisymm (Subgroup.map_subtype_le _)
  refine (Subgroup.closure_le _).mpr fun t ht => ?_
  obtain ⟨y, hy, rfl⟩ := class_conj_in_closure hz huniq h1 hT hzT hx'T hx' ht
  refine ⟨⟨y, hy⟩⁻¹ * zY * ⟨y, hy⟩, Subgroup.subset_closure ⟨⟨y, hy⟩, rfl⟩, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
  rfl

theorem unique_subgroupOf (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H)
    (Y : Subgroup G) (hzY : z ∈ Y) :
    ∀ g : Y, (⟨z, hzY⟩ : Y) ∈ rightConjugate (H.subgroupOf Y) g ↔ g ∈ H.subgroupOf Y := by
  intro g
  rw [mem_rightConjugate_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have h := huniq g
  rw [mem_rightConjugate_iff] at h
  exact h

theorem productUnique_subgroupOf (h1 : ProductUniqueContainment H z) (Y : Subgroup G)
    (hzY : z ∈ Y) : ProductUniqueContainment (H.subgroupOf Y) ⟨z, hzY⟩ := by
  intro t ht hzt hne g
  have htG : (t : G) ∈ involutionPointClass z := by
    obtain ⟨k, hk⟩ := ht
    exact ⟨k, congrArg Subtype.val hk⟩
  have hztG : Commute z (t : G) := congrArg Subtype.val hzt
  have hneG : (t : G) ≠ z := fun h => hne (Subtype.ext h)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact h1 t htG hztG hneG g

theorem centralProduct_subgroupOf [Finite G] (hz : orderOf z = 2)
    (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) (h2 : CentralProductCentralizer H z)
    (Y : Subgroup G) (hzY : z ∈ Y) (hYH : ¬ Y ≤ H) :
    CentralProductCentralizer (H.subgroupOf Y) ⟨z, hzY⟩ := by
  have h1 := productUniqueContainment_of_centralProductCentralizer hz huniq h2
  have hzY2 : orderOf (⟨z, hzY⟩ : Y) = 2 := (Subgroup.orderOf_mk z hzY).trans hz
  have hne : H.subgroupOf Y ≠ ⊤ := by
    intro h
    apply hYH
    intro y hy
    have hmem : (⟨y, hy⟩ : Y) ∈ H.subgroupOf Y := h ▸ Subgroup.mem_top _
    exact hmem
  exact centralProductCentralizer_of_productUniqueContainment hzY2 (unique_subgroupOf huniq Y hzY)
    hne (productUnique_subgroupOf h1 Y hzY)

end CFSG.ComponentClassification.AschbacherStrongEmbedding
