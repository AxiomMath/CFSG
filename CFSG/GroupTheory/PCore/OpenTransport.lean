module

public import CFSG.Assembly.Defs

public section

namespace CFSG

theorem openPCoreOf_eq_map_pCore (p : ℕ) {G : Type*} [Group G] (H : Subgroup G) :
    Open.pCoreOf p H = (CFSG.pCore p H).map H.subtype := by
  rw [Open.pCoreOf]

theorem Assembly.pCoreOf_eq_open (p : ℕ) {G : Type*} [Group G] (H : Subgroup G) :
    Assembly.pCoreOf p H = Open.pCoreOf p H :=
  rfl

theorem mem_openPCoreOf_iff {p : ℕ} {G : Type*} [Group G] {H : Subgroup G} (x : H) :
    (x : G) ∈ Open.pCoreOf p H ↔ x ∈ CFSG.pCore p H := by
  rw [openPCoreOf_eq_map_pCore]
  exact Subgroup.mem_map_iff_mem H.subtype_injective

theorem mem_openPCoreOf_iff_open {p : ℕ} {G : Type*} [Group G] {H : Subgroup G} (x : H) :
    (x : G) ∈ Open.pCoreOf p H ↔ x ∈ Open.pCore p H :=
  Subgroup.mem_map_iff_mem H.subtype_injective

theorem openPCoreOf_subgroupOf (p : ℕ) {G : Type*} [Group G] (H : Subgroup G) :
    (Open.pCoreOf p H).subgroupOf H = CFSG.pCore p H := by
  rw [openPCoreOf_eq_map_pCore, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective]

theorem openPCoreOf_le (p : ℕ) {G : Type*} [Group G] (H : Subgroup G) : Open.pCoreOf p H ≤ H :=
  Subgroup.map_subtype_le _

end CFSG
