module

public import CFSG.ClassicalInvolution.Asc77.AscE184Sub

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem omegaStarNbr_map {Y : Subgroup G} {K' J' : Subgroup Y}
    (h : J' ∈ omegaStarNbr (restrictFamily Ω Y) K') :
    J'.map Y.subtype ∈ omegaStarNbr Ω (K'.map Y.subtype) :=
  omegaStarNbr_of_restrict (Subgroup.map_subtype_le K') (Subgroup.map_subtype_le J')
    (by rwa [subgroupOf_map_subtype', subgroupOf_map_subtype'])

theorem omegaNbr_map {Y : Subgroup G} {K' J' : Subgroup Y}
    (h : J' ∈ omegaNbr (restrictFamily Ω Y) K') :
    J'.map Y.subtype ∈ omegaNbr Ω (K'.map Y.subtype) :=
  omegaNbr_of_restrict (Subgroup.map_subtype_le K') (Subgroup.map_subtype_le J')
    (by rwa [subgroupOf_map_subtype', subgroupOf_map_subtype'])

theorem dstarAdj_map {Y : Subgroup G} {K' J' : Subgroup Y}
    (h : dstarAdj (restrictFamily Ω Y) K' J') :
    dstarAdj Ω (K'.map Y.subtype) (J'.map Y.subtype) := by
  obtain ⟨hJ', h | h⟩ := h
  · exact ⟨mem_restrictFamily_iff.mp hJ', Or.inl (omegaStarNbr_map h)⟩
  · exact ⟨mem_restrictFamily_iff.mp hJ', Or.inr (omegaStarNbr_map h)⟩

theorem dstarComp_map {Y : Subgroup G} {K' J' : Subgroup Y}
    (h : J' ∈ dstarComp (restrictFamily Ω Y) K') :
    J'.map Y.subtype ∈ dstarComp Ω (K'.map Y.subtype) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (dstarAdj_map hbc)

theorem mem_of_mem_dstarComp {K J : Subgroup G} (h : J ∈ dstarComp Ω K) (hne : J ≠ K) :
    J ∈ Ω := by
  induction h with
  | refl => exact absurd rfl hne
  | tail _ hbc _ => exact hbc.1

theorem kPerp_map {Y : Subgroup G} {K' J' : Subgroup Y}
    (h : J' ∈ KPerp (restrictFamily Ω Y) K') :
    J'.map Y.subtype ∈ KPerp Ω (K'.map Y.subtype) := by
  rcases h with rfl | h
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (omegaNbr_map h)

theorem twinSet_map {Y K : Subgroup G} (hKY : K ≤ Y) {L' : Subgroup Y}
    (h : L' ∈ twinSet (restrictFamily Ω Y) (K.subgroupOf Y)) :
    L'.map Y.subtype ∈ twinSet Ω K := by
  obtain ⟨hL', z, hzK, hzL⟩ := h
  refine ⟨mem_restrictFamily_iff.mp hL', (z : G), isUniqueInvolution_of_subgroupOf hzK hKY, ?_⟩
  exact isUniqueInvolution_of_subgroupOf (by rwa [subgroupOf_map_subtype'])
    (Subgroup.map_subtype_le L')

theorem dstarComp_subset_insert (K : Subgroup G) : dstarComp Ω K ⊆ insert K Ω := by
  intro J hJ
  by_cases h : J = K
  · exact Or.inl h
  · exact Or.inr (mem_of_mem_dstarComp hJ h)

theorem trans_top_of_transitive {K : Subgroup G} (hall : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) :
    ∀ J ∈ dstarComp Ω K, ∃ h ∈ (⊤ : Subgroup G), conjSub h K = J := by
  intro J hJ
  rcases dstarComp_subset_insert K hJ with rfl | hJΩ
  · exact ⟨1, Subgroup.mem_top _, conjSub_one _⟩
  · obtain ⟨g, hg⟩ := hall J hJΩ
    exact ⟨g, Subgroup.mem_top _, hg⟩

theorem eHyp_top {K : Subgroup G} (W : Subgroup G) (hall : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) :
    EHyp Ω K W ⊤ :=
  ⟨trans_top_of_transitive hall, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => le_top⟩

end CFSG.ClassicalInvolution.Asc77
