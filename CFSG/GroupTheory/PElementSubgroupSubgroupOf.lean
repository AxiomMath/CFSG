module

public import CFSG.RankThree.PartOne.S12.Hyp
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG

open CFSG.RankThree.PartOne

theorem pElementSubgroup_subgroupOf_self {G : Type} [Group G] (p : ℕ) (L : Subgroup G) :
    (pElementSubgroup p L).subgroupOf L = pElementSubgroup p (⊤ : Subgroup ↥L) := by
  have hmap : (pElementSubgroup p (⊤ : Subgroup ↥L)).map L.subtype = pElementSubgroup p L := by
    rw [pElementSubgroup, pElementSubgroup, MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨-, k, hk⟩, rfl⟩
      exact ⟨y.2, k, (Subgroup.orderOf_coe y).trans hk⟩
    · rintro ⟨hxL, k, hk⟩
      exact ⟨⟨x, hxL⟩, ⟨trivial, k, by rwa [← Subgroup.orderOf_coe]⟩, rfl⟩
  have hle : pElementSubgroup p L ≤ L := (Subgroup.closure_le L).mpr fun _ hx => hx.1
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hle, hmap]

end CFSG
