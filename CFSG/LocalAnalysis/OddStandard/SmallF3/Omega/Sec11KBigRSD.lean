module

public import CFSG.Open.Catalog
import CFSG.CharacterTheory.Semidihedral.CentralQuotients
import CFSG.GroupTheory.QuasiDihedralFusion.SemidihedralModel

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private lemma semidihedral_involution_eq_z {P : Subgroup G} {n : ℕ} (hn : 4 ≤ n)
    (e : ↥P ≃* CFSG.Open.SemidihedralGroup n) {z : G} (hzP : z ∈ P)
    (hz2 : orderOf z = 2) (hzc : ∀ x ∈ P, x * z = z * x) :
    e ⟨z, hzP⟩ = CFSG.Semidihedral.z n := by
  refine CFSG.Semidihedral.CentralQuotients.original_center_unique_involution n hn _ ?_ ?_
  · rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzc (y : G) y.2)
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz2]

theorem s900_sd_quaternion {P : Subgroup G} {n : ℕ} (hn : 4 ≤ n)
    (hP : Nonempty (↥P ≃* CFSG.Open.SemidihedralGroup n)) {z : G} (hzP : z ∈ P)
    (hz2 : orderOf z = 2) (hzc : ∀ x ∈ P, x * z = z * x) :
    ∃ Q : Subgroup G, Q ≤ P ∧ Q.relIndex P = 2 ∧ ∀ s ∈ Q, orderOf s = 2 → s = z := by
  classical
  let e : ↥P ≃* CFSG.Open.SemidihedralGroup n := Classical.choice hP
  let ψ : CFSG.Open.SemidihedralGroup n →* G := P.subtype.comp e.symm.toMonoidHom
  have hψinj : Function.Injective ψ := by
    intro a b hab
    exact e.symm.injective (Subtype.coe_injective (by simpa [ψ] using hab))
  have hA : e ⟨z, hzP⟩ = CFSG.Semidihedral.z n :=
    semidihedral_involution_eq_z hn e hzP hz2 hzc
  have hpsi_z : ψ (CFSG.Semidihedral.z n) = z := by
    have h := congrArg (fun a : ↥P => (a : G)) (congrArg e.symm hA)
    simpa [ψ] using h.symm
  let Q : Subgroup G := (CFSG.Semidihedral.quaternionSubgroup n).map ψ
  have hQP : Q ≤ P := by
    intro x hx
    change x ∈ (CFSG.Semidihedral.quaternionSubgroup n).map ψ at hx
    rcases Subgroup.mem_map.mp hx with ⟨g, -, rfl⟩
    exact (e.symm g).2
  have hQsub : Q.subgroupOf P =
      (CFSG.Semidihedral.quaternionSubgroup n).map
        (e.symm : CFSG.Open.SemidihedralGroup n →* ↥P) := by
    ext x
    constructor
    · intro hx
      change (x : G) ∈ (CFSG.Semidihedral.quaternionSubgroup n).map ψ at hx
      rcases Subgroup.mem_map.mp hx with ⟨g, hg, hgx⟩
      exact Subgroup.mem_map.mpr ⟨g, hg, Subtype.ext (by simpa [ψ] using hgx)⟩
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨g, hg, hgx⟩
      rw [← hgx]
      exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
  refine ⟨Q, hQP, ?_, ?_⟩
  · show (Q.subgroupOf P).index = 2
    rw [hQsub, Subgroup.index_map_equiv,
      CFSG.Semidihedral.quaternionSubgroup_index n (by omega)]
  · intro s hsQ hs2
    change s ∈ (CFSG.Semidihedral.quaternionSubgroup n).map ψ at hsQ
    rcases Subgroup.mem_map.mp hsQ with ⟨g, hg, hgs⟩
    have hg2 : orderOf g = 2 := by
      rw [← orderOf_injective ψ hψinj g, hgs, hs2]
    rw [← hgs,
      CFSG.Semidihedral.quaternion_unique_involution n (by omega) g hg hg2, hpsi_z]

theorem s900_sd_noncentral_conj {P : Subgroup G} {n : ℕ} (hn : 4 ≤ n)
    (hP : Nonempty (↥P ≃* CFSG.Open.SemidihedralGroup n)) {z : G} (hzP : z ∈ P)
    (hz2 : orderOf z = 2) (hzc : ∀ x ∈ P, x * z = z * x) :
    ∃ u ∈ P, orderOf u = 2 ∧ u ≠ z ∧
      ∀ s ∈ P, orderOf s = 2 → s ≠ z → ∃ p ∈ P, p * s * p⁻¹ = u := by
  classical
  let e : ↥P ≃* CFSG.Open.SemidihedralGroup n := Classical.choice hP
  let ψ : CFSG.Open.SemidihedralGroup n →* G := P.subtype.comp e.symm.toMonoidHom
  have hψinj : Function.Injective ψ := by
    intro a b hab
    exact e.symm.injective (Subtype.coe_injective (by simpa [ψ] using hab))
  have hA : e ⟨z, hzP⟩ = CFSG.Semidihedral.z n :=
    semidihedral_involution_eq_z hn e hzP hz2 hzc
  have hpsi_z : ψ (CFSG.Semidihedral.z n) = z := by
    have h := congrArg (fun a : ↥P => (a : G)) (congrArg e.symm hA)
    simpa [ψ] using h.symm
  refine ⟨ψ (CFSG.Semidihedral.s n), (e.symm (CFSG.Semidihedral.s n)).2, ?_, ?_, ?_⟩
  · rw [orderOf_injective ψ hψinj, CFSG.Semidihedral.orderOf_s n (by omega)]
  · intro h
    have hsz : CFSG.Semidihedral.s n = CFSG.Semidihedral.z n := by
      apply hψinj
      rw [h, hpsi_z]
    exact CFSG.QuasiDihedralFusion.s_ne_z hn hsz
  · intro s hsP hs2 hsz
    let g : CFSG.Open.SemidihedralGroup n := e ⟨s, hsP⟩
    have hg2 : orderOf g = 2 := by
      dsimp only [g]
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hs2]
    have hg_ne : g ≠ CFSG.Semidihedral.z n := by
      intro h
      apply hsz
      have h2 : (⟨s, hsP⟩ : ↥P) = ⟨z, hzP⟩ := by
        apply e.injective
        dsimp only [g] at h
        exact h.trans hA.symm
      exact congrArg Subtype.val h2
    obtain ⟨c, hc⟩ := isConj_iff.mp
      ((CFSG.QuasiDihedralFusion.sd_involution_cases hn g hg2).resolve_left hg_ne)
    refine ⟨ψ c⁻¹, (e.symm c⁻¹).2, ?_⟩
    have hsc : ψ g = s := by
      dsimp only [g, ψ]
      simp
    have hconj : c⁻¹ * g * c = CFSG.Semidihedral.s n := by
      rw [← hc]
      group
    calc ψ c⁻¹ * s * (ψ c⁻¹)⁻¹
        = ψ c⁻¹ * ψ g * (ψ c⁻¹)⁻¹ := by rw [hsc]
      _ = ψ (c⁻¹ * g * (c⁻¹)⁻¹) := by rw [← map_inv, ← map_mul, ← map_mul]
      _ = ψ (c⁻¹ * g * c) := by rw [inv_inv]
      _ = ψ (CFSG.Semidihedral.s n) := by rw [hconj]

end CFSG.OddStandard.SmallF3.Omega
