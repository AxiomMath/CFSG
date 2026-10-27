module

public import CFSG.ClassicalInvolution.Asc77.WP2Defs

public section

namespace CFSG.ClassicalInvolution.Asc77.T8T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem muAbelian_notE4_transfer_gen {W W' : Subgroup G}
    (e : ↥(muGroup Ω W) ≃* ↥(muGroup Ω W'))
    (hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) (hE4 : ¬ MuIsoE4 Ω W) :
    (∀ x ∈ muGroup Ω W', ∀ y ∈ muGroup Ω W', x * y = y * x) ∧ ¬ MuIsoE4 Ω W' := by
  refine ⟨fun x hx y hy => ?_, fun h => hE4 ?_⟩
  · have h1 : e.symm ⟨x, hx⟩ * e.symm ⟨y, hy⟩ = e.symm ⟨y, hy⟩ * e.symm ⟨x, hx⟩ :=
      Subtype.ext (hab _ (e.symm ⟨x, hx⟩).2 _ (e.symm ⟨y, hy⟩).2)
    have h2 := congrArg e h1
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h2
    exact congrArg Subtype.val h2
  · obtain ⟨φ⟩ := h
    exact ⟨e.trans φ⟩

end CFSG.ClassicalInvolution.Asc77.T8T
