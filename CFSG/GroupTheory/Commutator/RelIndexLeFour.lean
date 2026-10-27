module

public import CFSG.GroupTheory.Commutator.Quotient

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem commutator_le_of_relIndex_le_four {N H : Subgroup G} [Finite ↥H]
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (h4 : N.relIndex H ≤ 4) : ⁅H, H⁆ ≤ N := by
  haveI : (N.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  haveI : IsMulCommutative (↥H ⧸ N.subgroupOf H) :=
    CFSG.isMulCommutative_of_card_le_four h4
  have hle : _root_.commutator ↥H ≤ N.subgroupOf H :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hmap := (Subgroup.map_subtype_le_map_subtype (G' := H)).mpr hle
  rw [Subgroup.map_subtype_commutator, Subgroup.subgroupOf_map_subtype] at hmap
  exact hmap.trans inf_le_left

end CFSG.GroupTheory
