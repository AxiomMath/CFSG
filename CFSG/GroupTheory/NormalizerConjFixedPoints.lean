module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG

variable {G : Type*} [Group G]

theorem map_eqLocus_normalizerMonoidHom (H : Subgroup G) {b : G}
    (hb : b ∈ Subgroup.normalizer (H : Set G)) :
    ((MonoidHom.eqLocus (Subgroup.normalizerMonoidHom (H := H) ⟨b, hb⟩).toMonoidHom
        (MonoidHom.id H)).map H.subtype) = H ⊓ Subgroup.centralizer ({b} : Set G) := by
  ext x
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hfix : (Subgroup.normalizerMonoidHom (H := H) ⟨b, hb⟩) h = h := hh
    have hcoe := congrArg (fun y : H => (y : G)) hfix
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hcoe
    refine Subgroup.mem_inf.2 ⟨h.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have : b * (h : G) * b⁻¹ = (h : G) := hcoe
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  · intro hx
    obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.1 hx
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    apply Subtype.ext
    change ((Subgroup.normalizerMonoidHom (H := H) ⟨b, hb⟩) ⟨x, hxH⟩ : G) = x
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    have hcomm : b * x = x * b := Subgroup.mem_centralizer_iff.1 hxC b rfl
    show b * x * b⁻¹ = x
    rw [hcomm, mul_inv_cancel_right]

end CFSG

end
