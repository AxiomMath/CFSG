module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

open Matrix
open scoped commutatorElement

theorem uScal_central_conj {G : Type*} [Group G] {z : G} (hz : z ∈ Subgroup.center G) (x : G) :
    z * x * z⁻¹ = x := by
  rw [← Subgroup.mem_center_iff.1 hz x, mul_inv_cancel_right]

theorem uScal_commutator_central_left {G : Type*} [Group G] {z : G} (hz : z ∈ Subgroup.center G)
    (g h : G) : ⁅z * g, h⁆ = ⁅g, h⁆ := by
  have hzh : ⁅z, h⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hz h).symm
  rw [commutatorElement_mul_left_eq_conj_mul, hzh, mul_one, uScal_central_conj hz]

theorem uScal_commutator_central_right {G : Type*} [Group G] {z : G} (hz : z ∈ Subgroup.center G)
    (g h : G) : ⁅g, z * h⁆ = ⁅g, h⁆ := by
  have hgz : ⁅g, z⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hz g)
  rw [commutatorElement_mul_right_eq_mul_conj, hgz, one_mul, uScal_central_conj hz]

theorem uScal_exists_central_of_conj {K : Type} [Field K] {d : ℕ} (B g : GL (Fin d) K) {c : K}
    (h : (B : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) *
      ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = c • (g : Matrix (Fin d) (Fin d) K)) :
    ∃ z ∈ Subgroup.center (GL (Fin d) K), B * g * B⁻¹ = z * g := by
  refine ⟨B * g * B⁻¹ * g⁻¹, ?_, by group⟩
  rw [Subgroup.mem_center_iff]
  intro x
  apply Units.ext
  simp only [Units.val_mul, h, Matrix.smul_mul, Matrix.mul_smul, Units.mul_inv, mul_one, one_mul]

theorem uScal_commute_of_isPerfect {K : Type} [Field K] {d : ℕ} (H : Subgroup (GL (Fin d) K))
    [Group.IsPerfect H] (B : GL (Fin d) K)
    (hB : ∀ g ∈ H, ∃ c : K, (B : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) *
      ((B⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = c • (g : Matrix (Fin d) (Fin d) K)) :
    ∀ g ∈ H, B * g = g * B := by
  have hcomm : ∀ g ∈ H, ∀ h ∈ H, B * ⁅g, h⁆ = ⁅g, h⁆ * B := by
    intro g hg h hh
    obtain ⟨c, hc⟩ := hB g hg
    obtain ⟨c', hc'⟩ := hB h hh
    obtain ⟨z, hz, hzg⟩ := uScal_exists_central_of_conj B g hc
    obtain ⟨z', hz', hzh⟩ := uScal_exists_central_of_conj B h hc'
    have key : B * ⁅g, h⁆ * B⁻¹ = ⁅g, h⁆ := by
      have hmap := map_commutatorElement (MulAut.conj B) g h
      simp only [MulAut.conj_apply] at hmap
      rw [hmap, hzg, hzh, uScal_commutator_central_left hz, uScal_commutator_central_right hz']
    calc B * ⁅g, h⁆ = (B * ⁅g, h⁆ * B⁻¹) * B := by group
      _ = ⁅g, h⁆ * B := by rw [key]
  intro g hg
  let S : Subgroup H := (Subgroup.centralizer ({B} : Set (GL (Fin d) K))).subgroupOf H
  have hle : commutator H ≤ S := by
    show ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ ≤ S
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    rw [hb]
    have hxy : ((⁅x, y⁆ : H) : GL (Fin d) K) =
        ⁅(x : GL (Fin d) K), (y : GL (Fin d) K)⁆ := by
      simp [commutatorElement_def]
    rw [hxy]
    exact hcomm (x : GL (Fin d) K) x.2 (y : GL (Fin d) K) y.2
  have hmem : (⟨g, hg⟩ : H) ∈ commutator H := by
    rw [Group.IsPerfect.commutator_eq_top]
    exact Subgroup.mem_top _
  have hS := hle hmem
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hS
  exact hS B (Set.mem_singleton B)

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni

end
