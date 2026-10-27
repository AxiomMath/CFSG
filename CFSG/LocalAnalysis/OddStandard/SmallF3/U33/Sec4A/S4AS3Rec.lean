module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators
public import Mathlib.GroupTheory.Perm.Fin

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

theorem nonempty_perm_three_mulEquiv_dihedralGroup_three :
    Nonempty (Equiv.Perm (Fin 3) ≃* DihedralGroup 3) := by
  have hρ : orderOf (finRotate 3) = 3 := orderOf_eq_prime (by decide) (by decide)
  have hσ : orderOf (Equiv.swap (0 : Fin 3) 1) = 2 := orderOf_eq_prime (by decide) (by decide)
  have hgen : (⊤ : Subgroup (Equiv.Perm (Fin 3))) =
      Subgroup.zpowers (finRotate 3) ⊔ Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union, Set.singleton_union]
    have h := Equiv.Perm.closure_cycle_adjacent_swap (isCycle_finRotate (n := 1))
      (support_finRotate (n := 1)) 0
    exact h.symm
  have h := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem (finRotate 3)
    (Equiv.swap (0 : Fin 3) 1) hgen (by decide) (by decide) (fun hmem => by
      have hdvd := orderOf_dvd_of_mem_zpowers hmem
      rw [hρ, hσ] at hdvd
      norm_num at hdvd)
  rwa [hρ] at h

variable {G : Type*} [Group G]

theorem not_mem_zpowers_of_inverting {a b : G} (ha : orderOf a = 3) (hab : b * a * b⁻¹ = a⁻¹) :
    b ∉ zpowers a := by
  intro hb
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hc : a ^ k * a = a * a ^ k := (Commute.self_zpow a k).symm.eq
  have h1 : a ^ k * a * (a ^ k)⁻¹ = a := by
    rw [hc]
    group
  have h2 : a = a⁻¹ := h1.symm.trans hab
  have h3 : a ^ 2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr h2
  have h4 := orderOf_dvd_of_pow_eq_one h3
  rw [ha] at h4
  omega

theorem nonempty_closure_mulEquiv_dihedralGroup_three [Finite G] {a b : G} (ha : orderOf a = 3)
    (hb : b * b = 1) (hab : b * a * b⁻¹ = a⁻¹) :
    Nonempty (Subgroup.closure ({a, b} : Set G) ≃* DihedralGroup 3) := by
  set H := Subgroup.closure ({a, b} : Set G)
  have haH : a ∈ H := Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := Subgroup.subset_closure (by simp)
  have hgen : (⊤ : Subgroup H) = Subgroup.zpowers ⟨a, haH⟩ ⊔ Subgroup.zpowers ⟨b, hbH⟩ := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union, ← Subgroup.closure_closure_coe_preimage (k := ({a, b} : Set G))]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    constructor
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
  have h := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem (D := H) ⟨a, haH⟩ ⟨b, hbH⟩
    hgen (Subtype.ext (by simpa [pow_two] using hb)) (Subtype.ext (by simpa using hab))
    (fun hmem => not_mem_zpowers_of_inverting ha hab (by
      obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff).mp hmem
      exact (Subgroup.mem_zpowers_iff).mpr ⟨k, by simpa using congrArg Subtype.val hk⟩))
  rwa [Subgroup.orderOf_mk, ha] at h

theorem nonempty_closure_mulEquiv_perm_three [Finite G] {a b : G} (ha : orderOf a = 3)
    (hb : b * b = 1) (hab : b * a * b⁻¹ = a⁻¹) :
    Nonempty (↥(Subgroup.closure ({a, b} : Set G)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e₁⟩ := nonempty_closure_mulEquiv_dihedralGroup_three ha hb hab
  obtain ⟨e₂⟩ := nonempty_perm_three_mulEquiv_dihedralGroup_three
  exact ⟨e₁.trans e₂.symm⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
