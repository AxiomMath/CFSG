module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup

section Dih

variable {K : Type} [Group K]

theorem exists_cyclic_odd_core (D : Subgroup K) {k : ℕ} [NeZero k]
    (φ : ↥D ≃* DihedralGroup k) :
    ∃ T : Subgroup K, IsCyclic ↥T ∧ ∀ y ∈ D, Odd (orderOf y) → y ∈ T := by
  set y₀ : K := ((φ.symm (DihedralGroup.r 1) : ↥D) : K) with hy₀
  refine ⟨Subgroup.zpowers y₀, inferInstance, ?_⟩
  intro y hy hodd
  have hord : orderOf (φ ⟨y, hy⟩) = orderOf y := by
    rw [MulEquiv.orderOf_eq]
    exact Subgroup.orderOf_mk y hy
  rcases hz : φ ⟨y, hy⟩ with i | i
  ·
    have h1 : DihedralGroup.r i = DihedralGroup.r 1 ^ i.val := by
      rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    have h2 : (⟨y, hy⟩ : ↥D) = φ.symm (DihedralGroup.r 1) ^ i.val := by
      rw [← map_pow, ← h1, ← hz]
      simp
    have h3 : y = y₀ ^ i.val := by
      have := congrArg (fun z : ↥D => (z : K)) h2
      simpa [hy₀] using this
    rw [h3]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y₀) _
  · exfalso
    rw [hz, DihedralGroup.orderOf_sr] at hord
    rw [← hord] at hodd
    exact (Nat.not_odd_iff_even.mpr even_two) hodd

theorem odd_commute_of_dihedral (D : Subgroup K) {k : ℕ} [NeZero k] (φ : ↥D ≃* DihedralGroup k)
    {a b : K} (ha : a ∈ D) (hb : b ∈ D) (hao : Odd (orderOf a)) (hbo : Odd (orderOf b)) :
    a * b = b * a := by
  obtain ⟨T, hT, hmem⟩ := exists_cyclic_odd_core D φ
  have haT := hmem a ha hao
  have hbT := hmem b hb hbo
  have := hT
  have h : (⟨a, haT⟩ : ↥T) * ⟨b, hbT⟩ = ⟨b, hbT⟩ * ⟨a, haT⟩ :=
    IsMulCommutative.is_comm.comm _ _
  exact congrArg Subtype.val h

theorem isCyclic_of_odd_le_dihedral (D : Subgroup K) {k : ℕ} [NeZero k]
    (φ : ↥D ≃* DihedralGroup k) {X : Subgroup K} (hXD : X ≤ D)
    (hXodd : ∀ x ∈ X, Odd (orderOf x)) : IsCyclic ↥X := by
  obtain ⟨T, hT, hmem⟩ := exists_cyclic_odd_core D φ
  have hXT : X ≤ T := fun x hx => hmem x (hXD hx) (hXodd x hx)
  have : IsCyclic ↥(X.subgroupOf T) := inferInstance
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hXT).toMonoidHom
    fun a => ⟨(Subgroup.subgroupOfEquivOfLe hXT).symm a,
      (Subgroup.subgroupOfEquivOfLe hXT).apply_symm_apply a⟩

end Dih

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
