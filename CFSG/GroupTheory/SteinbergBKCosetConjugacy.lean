module

public import Mathlib.Data.Set.Card
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.GroupTheory.SteinbergBK

theorem fixed_point_free_coset_conjugacy {G : Type*} [Group G] [Finite G] {H : Subgroup G} {e : G}
    (he : e ∈ Subgroup.normalizer (H : Set G)) (hfix : ∀ a ∈ H, a * e = e * a → a = 1) :
    Set.BijOn (fun a => a⁻¹ * e * a) (H : Set G) {x | ∃ h ∈ H, h * e = x} ∧
      (fun a => a⁻¹ * e * a) '' (H : Set G) = {x | ∃ h ∈ H, h * e = x} := by
  have hmaps : Set.MapsTo (fun a => a⁻¹ * e * a) (H : Set G) {x | ∃ h ∈ H, h * e = x} := by
    intro a ha
    refine ⟨a⁻¹ * (e * a * e⁻¹), mul_mem (inv_mem ha)
      ((Subgroup.mem_normalizer_iff.mp he a).mp ha), ?_⟩
    group
  have hinj : Set.InjOn (fun a => a⁻¹ * e * a) (H : Set G) := by
    intro a ha b hb hab
    have hcomm : (a * b⁻¹) * e = e * (a * b⁻¹) := by
      have h : a⁻¹ * e * a = b⁻¹ * e * b := hab
      calc a * b⁻¹ * e = a * (b⁻¹ * e * b) * b⁻¹ := by group
        _ = a * (a⁻¹ * e * a) * b⁻¹ := by rw [h]
        _ = e * (a * b⁻¹) := by group
    have h1 := hfix _ (mul_mem ha (inv_mem hb)) hcomm
    exact mul_inv_eq_one.mp h1
  have hcard : Set.ncard {x | ∃ h ∈ H, h * e = x} = Set.ncard (H : Set G) := by
    have himage : {x | ∃ h ∈ H, h * e = x} = (fun h => h * e) '' (H : Set G) := by
      ext x
      exact ⟨fun ⟨h, hh, hx⟩ => ⟨h, hh, hx⟩, fun ⟨h, hh, hx⟩ => ⟨h, hh, hx⟩⟩
    rw [himage, Set.ncard_image_of_injective _ (mul_left_injective e)]
  have hsurj : Set.SurjOn (fun a => a⁻¹ * e * a) (H : Set G) {x | ∃ h ∈ H, h * e = x} := by
    have himg : (fun a => a⁻¹ * e * a) '' (H : Set G) ⊆ {x | ∃ h ∈ H, h * e = x} :=
      hmaps.image_subset
    have heq := Set.eq_of_subset_of_ncard_le himg (by
      rw [hcard, hinj.ncard_image]) (Set.toFinite _)
    rw [Set.SurjOn, ← heq]
  exact ⟨⟨hmaps, hinj, hsurj⟩, Set.BijOn.image_eq ⟨hmaps, hinj, hsurj⟩⟩

end CFSG.GroupTheory.SteinbergBK
