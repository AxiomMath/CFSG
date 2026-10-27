module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.GH74.GLS.LU

open scoped commutatorElement

section Lift

variable {Ĝ X : Type*} [Group Ĝ] [Group X]

theorem eq_one_of_mul_self_eq_one_of_pow_three_eq_one {G : Type*} [Group G] {k : G}
    (h2 : k * k = 1) (h3 : k ^ 3 = 1) : k = 1 := by
  have : k = k ^ 3 * (k * k)⁻¹ := by group
  rw [this, h3, h2]
  simp

theorem commute_of_involution_lift (α : Ĝ →* X) (hker : α.ker ≤ Subgroup.center Ĝ)
    (hZ : ∀ k ∈ Subgroup.center Ĝ, k ^ 3 = 1) {z : Ĝ} (hz : z * z = 1) {g : Ĝ}
    (hg : α g * α z = α z * α g) : g * z = z * g := by
  set k := g * z * g⁻¹ * z⁻¹ with hk
  have hkker : k ∈ α.ker := by
    rw [MonoidHom.mem_ker, hk, map_mul, map_mul, map_mul, map_inv, map_inv, hg]
    group
  have hkc := hker hkker
  have hk3 := hZ k hkc
  have e : g * z * g⁻¹ = k * z := by rw [hk]; group
  have e2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz]; group
  rw [e] at e2
  have hzk : z * k = k * z := Subgroup.mem_center_iff.mp hkc z
  have e3 : k * z * (k * z) = k * k * (z * z) := by
    calc k * z * (k * z) = k * (z * k) * z := by group
      _ = k * (k * z) * z := by rw [hzk]
      _ = k * k * (z * z) := by group
  rw [e3, hz, mul_one] at e2
  have hk1 := eq_one_of_mul_self_eq_one_of_pow_three_eq_one e2 hk3
  rw [hk1] at e
  have h' : g * z * g⁻¹ = z := by rw [e]; simp
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [h']

theorem exists_involution_lift (α : Ĝ →* X) (hker : α.ker ≤ Subgroup.center Ĝ)
    (hZ : ∀ k ∈ Subgroup.center Ĝ, k ^ 3 = 1) {a : X} (ha : a ∈ α.range) (ha2 : a * a = 1) :
    ∃ z : Ĝ, z * z = 1 ∧ α z = a := by
  obtain ⟨g, rfl⟩ := ha
  have hg2 : g * g ∈ α.ker := by rw [MonoidHom.mem_ker, map_mul]; exact ha2
  have h3 := hZ _ (hker hg2)
  refine ⟨g ^ 3, ?_, ?_⟩
  · calc g ^ 3 * g ^ 3 = (g * g) ^ 3 := ((Commute.refl g).mul_pow 3).symm
      _ = 1 := h3
  · rw [map_pow]
    calc α g ^ 3 = α g * (α g * α g) := pow_three _
      _ = α g := by rw [ha2, mul_one]

theorem le_map_of_commutator_le (α : Ĝ →* X) {C L : Subgroup Ĝ} (hCL : ⁅C, C⁆ ≤ L)
    {U : Subgroup X} (hU : ⁅U, U⁆ = U) (hUC : ∀ u ∈ U, ∃ g ∈ C, α g = u) : U ≤ L.map α := by
  have h1 : U ≤ C.map α := fun u hu => by
    obtain ⟨g, hg, rfl⟩ := hUC u hu
    exact ⟨g, hg, rfl⟩
  calc U = ⁅U, U⁆ := hU.symm
    _ ≤ ⁅C.map α, C.map α⁆ := Subgroup.commutator_mono h1 h1
    _ = (⁅C, C⁆).map α := (Subgroup.map_commutator C C α).symm
    _ ≤ L.map α := Subgroup.map_mono hCL

theorem commutator_self_of_isPerfect {H : Type*} [Group H] (U : Subgroup H)
    (hU : Group.IsPerfect U) : ⁅U, U⁆ = U := by
  have h1 : ⁅(⊤ : Subgroup U), (⊤ : Subgroup U)⁆ = ⊤ := hU.commutator_eq_top
  have h2 := Subgroup.map_commutator (⊤ : Subgroup U) (⊤ : Subgroup U) U.subtype
  simp only [h1, Subgroup.map_top, Subgroup.range_subtype] at h2
  exact h2.symm

end Lift

end CFSG.GH74.GLS.LU
