module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

variable {G : Type*} [Group G]

theorem inv_conj_of_fixed_point {T U : Subgroup G} {f : G} (hUT : U ≤ T)
    (hUn : U.relIndex T = 2)
    (hfix : ∀ x ∈ T, x ∉ U → x * x = 1 →
      ∃ z ∈ T, x * (z⁻¹ * f ^ 2 * z) = (z⁻¹ * f ^ 2 * z) * x) :
    ∀ x ∈ T, x ∉ U → x * x = 1 →
      ∃ z ∈ T, (z * x * z⁻¹) * f ^ 2 = f ^ 2 * (z * x * z⁻¹) ∧ z * x * z⁻¹ ∉ U := by
  have hn : (U.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hUn
  have hQn : ∀ t ∈ T, ∀ q ∈ U, t * q * t⁻¹ ∈ U := fun t ht q hq =>
    Subgroup.mem_subgroupOf.1
      (hn.conj_mem ⟨q, hUT hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨t, ht⟩)
  intro x hxT hxU hxx
  obtain ⟨z, hzT, hz⟩ := hfix x hxT hxU hxx
  refine ⟨z, hzT, ?_, ?_⟩
  · calc (z * x * z⁻¹) * f ^ 2 = z * (x * (z⁻¹ * f ^ 2 * z)) * z⁻¹ := by group
      _ = z * ((z⁻¹ * f ^ 2 * z) * x) * z⁻¹ := by rw [hz]
      _ = f ^ 2 * (z * x * z⁻¹) := by group
  · intro h
    apply hxU
    have := hQn z⁻¹ (T.inv_mem hzT) _ h
    have e : z⁻¹ * (z * x * z⁻¹) * z⁻¹⁻¹ = x := by group
    rwa [e] at this

end CFSG.EvenSporadicStandard.TwoHS
