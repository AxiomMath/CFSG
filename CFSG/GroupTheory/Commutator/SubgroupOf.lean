module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.GroupTheory.Commutator.Basic

public section

namespace CFSG.GroupTheory

open Subgroup

theorem commutator_subgroupOf_eq {G : Type*} [Group G] {A B H : Subgroup G}
    (hA : A ≤ H) (hB : B ≤ H) :
    ⁅A.subgroupOf H, B.subgroupOf H⁆ = (⁅A, B⁆).subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le hA hB)]

theorem map_subgroupOf_le_normalizer {G H : Type*} [Group G] [Group H] {M B X : Subgroup G}
    (f : ↥M →* H) (h : B ≤ Subgroup.normalizer (X : Set G)) :
    (B.subgroupOf M).map f ≤
      Subgroup.normalizer (((X.subgroupOf M).map f : Subgroup H) : Set H) := by
  refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map f)
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using
    Subgroup.mem_normalizer_iff.1 (h (Subgroup.mem_subgroupOf.mp hb)) (x : G)

theorem commutator_zpowers_map_subgroupOf_eq {G H : Type*} [Group G] [Group H]
    {M X : Subgroup G} (f : ↥M →* H) {b : G} (hbM : b ∈ M) (hXM : X ≤ M)
    (h : ⁅Subgroup.zpowers b, X⁆ = X) :
    ⁅Subgroup.zpowers (f ⟨b, hbM⟩), (X.subgroupOf M).map f⁆ = (X.subgroupOf M).map f := by
  have hzp : (Subgroup.zpowers b).subgroupOf M = Subgroup.zpowers (⟨b, hbM⟩ : ↥M) := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr hbM), MonoidHom.map_zpowers]
    rfl
  rw [← MonoidHom.map_zpowers f ⟨b, hbM⟩, ← Subgroup.map_commutator, ← hzp,
    commutator_subgroupOf_eq (Subgroup.zpowers_le.mpr hbM) hXM, h]

end CFSG.GroupTheory
