module

public import CFSG.LocalAnalysis.QuasithinUnique.ComponentEmbeddingLayer
public import CFSG.LocalAnalysis.QuasithinUnique.BenderInterfaces

public section

namespace CFSG.QuasithinUnique.ComponentEmbedding

open Subgroup CFSG.ComponentClassification OuterAutomorphisms

variable {G : Type*} [Group G]

theorem isComponentIn_map_subtype {H : Subgroup G} {K' : Subgroup H} (hK' : CFSG.IsComponent K') :
    IsComponentIn (K'.map H.subtype) H := by
  refine ⟨map_subtype_le K', ?_⟩
  have h : (K'.map H.subtype).subgroupOf H = K' :=
    comap_map_eq_self_of_injective H.subtype_injective K'
  rwa [h]

theorem mem_map_subtype_iff {H : Subgroup G} {K' : Subgroup H} {x : H} :
    (x : G) ∈ K'.map H.subtype ↔ x ∈ K' :=
  mem_map_iff_mem H.subtype_injective

variable [Finite G]

theorem exists_isComponentIn_of_isComponentIn_inf_centralizer {H : Subgroup G}
    (hcore : CFSG.oddCore H = ⊥) {t : G} (htH : t ∈ H) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hnorm : ∀ K : Subgroup G, IsComponentIn K H → t ∈ normalizer (K : Set G))
    (hout : ∀ K : Subgroup G, IsComponentIn K H → Group.IsSolvable (Outer (K ⧸ center K)))
    {L : Subgroup G} (hL : IsComponentIn L (H ⊓ centralizer ({t} : Set G))) :
    ∃ K : Subgroup G, IsComponentIn K H ∧ L ≤ K := by
  let tH : H := ⟨t, htH⟩
  have htord : orderOf tH = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa using ht2)
    · intro h
      exact ht1 (congrArg Subtype.val h)
  have htK : ∀ K' : Subgroup H, CFSG.IsComponent K' → tH ∈ normalizer (K' : Set H) := by
    intro K' hK'
    have h := mem_normalizer_iff.1 (hnorm _ (isComponentIn_map_subtype hK'))
    refine mem_normalizer_iff.2 fun x => ?_
    exact (mem_map_subtype_iff (K' := K')).symm.trans
      ((h (x : G)).trans (mem_map_subtype_iff (K' := K') (x := tH * x * tH⁻¹)))
  have hout' : ∀ K' : Subgroup H, CFSG.IsComponent K' →
      Group.IsSolvable (Outer (K' ⧸ center K')) := by
    intro K' hK'
    have h := hout _ (isComponentIn_map_subtype hK')
    exact solvable_centerQuotient_of_equiv
      (K'.equivMapOfInjective H.subtype H.subtype_injective).symm
  have hC : (H ⊓ centralizer ({t} : Set G)).subgroupOf H = centralizer ({tH} : Set H) := by
    ext x
    rw [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, hx⟩
      exact Subtype.ext hx
    · intro hx
      exact ⟨x.2, congrArg Subtype.val hx⟩
  let e₁ : ↥((H ⊓ centralizer ({t} : Set G)).subgroupOf H) ≃*
      ↥(H ⊓ centralizer ({t} : Set G)) := subgroupOfEquivOfLe inf_le_left
  have hL' : CFSG.IsComponent
      ((L.subgroupOf (H ⊓ centralizer ({t} : Set G))).map e₁.symm.toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv e₁.symm hL.2
  obtain ⟨K', hK', hLK'⟩ :=
    odd_core_free_involution_Schreier_component_embedding_of_eq hcore htord htK hout' hC hL'
  refine ⟨K'.map H.subtype, isComponentIn_map_subtype hK', fun x hx => ?_⟩
  have hxC : x ∈ H ⊓ centralizer ({t} : Set G) := hL.1 hx
  have hmem : (⟨x, hxC.1⟩ : H) ∈ K' :=
    hLK' ⟨e₁.symm ⟨x, hxC⟩, ⟨⟨x, hxC⟩, hx, rfl⟩, rfl⟩
  exact ⟨⟨x, hxC.1⟩, hmem, rfl⟩

end CFSG.QuasithinUnique.ComponentEmbedding
