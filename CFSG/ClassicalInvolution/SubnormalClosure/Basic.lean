module

public import CFSG.ClassicalInvolution.Basic
public import CFSG.LocalAnalysis.ComponentClassification.Components

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open

variable {G : Type*} [Group G]

theorem isSubnormal_subgroupOf {A B : Subgroup G} (h : IsSubnormal A B) (H : Subgroup G) :
    IsSubnormal (A.subgroupOf H) (B.subgroupOf H) :=
  h.comap H.subtype

@[expose] def subnormalClosure (K : Subgroup G) : Subgroup G :=
  sInf {H : Subgroup G | K ≤ H ∧ IsSubnormal H ⊤}

theorem le_subnormalClosure (K : Subgroup G) : K ≤ subnormalClosure K :=
  le_sInf fun _ hH => hH.1

theorem subnormalClosure_le {K H : Subgroup G} (hKH : K ≤ H) (hH : IsSubnormal H ⊤) :
    subnormalClosure K ≤ H :=
  sInf_le ⟨hKH, hH⟩

theorem isSubnormal_subnormalClosure [Finite G] (K : Subgroup G) :
    IsSubnormal (subnormalClosure K) ⊤ := by
  have hclosed : InfClosed {H : Subgroup G | K ≤ H ∧ IsSubnormal H ⊤} := by
    rintro A ⟨hKA, hA⟩ B ⟨hKB, hB⟩
    refine ⟨le_inf hKA hKB, ?_⟩
    have := isSubnormal_inf hA B
    rw [top_inf_eq] at this
    exact isSubnormal_trans this hB
  exact (hclosed.sInf_mem (Set.toFinite _) ⟨le_top, IsSubnormal.refl ⊤⟩ subset_rfl).2

theorem isSubnormal_subnormalClosure_iff [Finite G] (K : Subgroup G) :
    IsSubnormal K (subnormalClosure K) ↔ IsSubnormal K ⊤ :=
  ⟨fun h => isSubnormal_trans h (isSubnormal_subnormalClosure K), fun h => by
    rw [← le_antisymm (le_subnormalClosure K) (subnormalClosure_le le_rfl h)]
    exact IsSubnormal.refl K⟩

theorem isSubnormal_top_map_subtype {H : Subgroup G} (hH : IsSubnormal H ⊤) {L : Subgroup H}
    (hL : IsSubnormal L ⊤) : IsSubnormal (L.map H.subtype) ⊤ := by
  have := CFSG.ComponentClassification.Components.chain_map H.subtype hL
  rw [Subgroup.map_top, Subgroup.range_subtype] at this
  exact isSubnormal_trans this hH

theorem map_subnormalClosure_subgroupOf [Finite G] {K H : Subgroup G} (hKH : K ≤ H)
    (hH : IsSubnormal H ⊤) :
    (subnormalClosure (K.subgroupOf H)).map H.subtype = subnormalClosure K := by
  have hM : subnormalClosure K ≤ H := subnormalClosure_le hKH hH
  refine le_antisymm ?_ ?_
  · rw [← Subgroup.map_subgroupOf_eq_of_le hM]
    refine Subgroup.map_mono (subnormalClosure_le ?_ ?_)
    · exact Subgroup.subgroupOf_mono H (le_subnormalClosure K)
    · have := isSubnormal_subgroupOf (isSubnormal_subnormalClosure K) H
      rwa [Subgroup.top_subgroupOf] at this
  · refine subnormalClosure_le ?_ (isSubnormal_top_map_subtype hH (isSubnormal_subnormalClosure _))
    have := Subgroup.map_mono (f := H.subtype) (le_subnormalClosure (K.subgroupOf H))
    rwa [Subgroup.map_subgroupOf_eq_of_le hKH] at this

theorem subnormalClosure_subgroupOf_subnormalClosure [Finite G] (K : Subgroup G) :
    subnormalClosure (K.subgroupOf (subnormalClosure K)) = ⊤ := by
  apply Subgroup.map_injective (Subgroup.subtype_injective (subnormalClosure K))
  rw [map_subnormalClosure_subgroupOf (le_subnormalClosure K) (isSubnormal_subnormalClosure K),
    Subgroup.map_top, Subgroup.range_subtype]

end CFSG.ClassicalInvolution
