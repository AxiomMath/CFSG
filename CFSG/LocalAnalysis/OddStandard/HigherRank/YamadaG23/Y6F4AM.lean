module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

open scoped commutatorElement

variable {C Y : Type} [Group C] [Group Y] {π : C →* Y}

private lemma commutatorElement_mul_central {G : Type*} [Group G] {k k' z z' : G}
    (hz : z ∈ Subgroup.center G) (hz' : z' ∈ Subgroup.center G) :
    ⁅k * z, k' * z'⁆ = ⁅k, k'⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hz1 : ⁅z, k' * z'⁆ = 1 := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      Commute.commutator_eq (Subgroup.mem_center_iff.mp hz k').symm,
      Commute.commutator_eq (Subgroup.mem_center_iff.mp hz z').symm]
    group
  have hk1 : ⁅k, k' * z'⁆ = ⁅k, k'⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj,
      Commute.commutator_eq (Subgroup.mem_center_iff.mp hz' k)]
    group
  rw [hz1, hk1]
  group

private lemma commutator_sup_central_le {G : Type*} [Group G] {K Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) : ⁅K ⊔ Z, K ⊔ Z⁆ ≤ ⁅K, K⁆ := by
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨k, hk, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨k', hk', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  rw [commutatorElement_mul_central (hZ hz) (hZ hz')]
  exact Subgroup.commutator_mem_commutator hk hk'

private lemma commutator_sup_central_eq {G : Type*} [Group G] {K Z : Subgroup G}
    (hZ : Z ≤ Subgroup.center G) : ⁅K ⊔ Z, K ⊔ Z⁆ = ⁅K, K⁆ :=
  le_antisymm (commutator_sup_central_le hZ)
    (Subgroup.commutator_mono le_sup_left le_sup_left)

private lemma comap_eq_sup_commutator_ker (hπ : Function.Surjective π)
    {B : Subgroup Y} (hB : Group.IsPerfect ↥B) :
    B.comap π = ⁅B.comap π, B.comap π⁆ ⊔ π.ker := by
  have hmap : ⁅B.comap π, B.comap π⁆.map π = B := by
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hπ B]
    exact Subgroup.isPerfect_iff.mp hB
  apply le_antisymm
  · intro r hr
    have hrB : π r ∈ B := Subgroup.mem_comap.mp hr
    have hrK : π r ∈ (⁅B.comap π, B.comap π⁆ : Subgroup C).map π := by
      rw [hmap]; exact hrB
    obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.mp hrK
    refine Subgroup.mem_sup_of_normal_right.mpr ⟨k, hk, k⁻¹ * r, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkπ]
    group
  · refine sup_le (Subgroup.commutator_le_self _) ?_
    intro r hr
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hr]
    exact B.one_mem

theorem y6f4a_perfect_lift (hπ : Function.Surjective π) (hker : π.ker ≤ center C)
    {B : Subgroup Y} (hB : Group.IsPerfect ↥B) :
    Group.IsPerfect ↥⁅B.comap π, B.comap π⁆ ∧ ⁅B.comap π, B.comap π⁆.map π = B ∧
      ⁅B.comap π, B.comap π⁆ ≤ B.comap π := by
  have hKleR : ⁅B.comap π, B.comap π⁆ ≤ B.comap π := Subgroup.commutator_le_self _
  have hmap : ⁅B.comap π, B.comap π⁆.map π = B := by
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hπ B]
    exact Subgroup.isPerfect_iff.mp hB
  have hsup : B.comap π = ⁅B.comap π, B.comap π⁆ ⊔ π.ker :=
    comap_eq_sup_commutator_ker hπ hB
  have hperfect : (⁅⁅B.comap π, B.comap π⁆, ⁅B.comap π, B.comap π⁆⁆ : Subgroup C) =
      ⁅B.comap π, B.comap π⁆ := by
    refine le_antisymm (Subgroup.commutator_le_self _) (le_of_eq ?_)
    calc ⁅B.comap π, B.comap π⁆
        = ⁅⁅B.comap π, B.comap π⁆ ⊔ π.ker, ⁅B.comap π, B.comap π⁆ ⊔ π.ker⁆ := by rw [← hsup]
      _ = ⁅⁅B.comap π, B.comap π⁆, ⁅B.comap π, B.comap π⁆⁆ :=
          commutator_sup_central_eq hker
  exact ⟨Subgroup.isPerfect_iff.mpr hperfect, hmap, hKleR⟩

end CFSG.OddStandard.HigherRank.YamadaG23
