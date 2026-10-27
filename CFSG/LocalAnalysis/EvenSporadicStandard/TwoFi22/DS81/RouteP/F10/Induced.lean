module

public import Mathlib.GroupTheory.QuotientGroup.Basic

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

variable {B Q : Type*} [Group B] [Group Q]

theorem exists_mulEquiv_induced (π : B →* Q) (hπ : Function.Surjective π) (γ : B ≃* B)
    (hγ : ∀ b, π (γ b) = 1 ↔ π b = 1) : ∃ γ' : Q ≃* Q, ∀ b, γ' (π b) = π (γ b) := by
  have hker : (π.ker).map (γ : B →* B) = π.ker := by
    ext x
    have hm : x ∈ (π.ker).map (γ : B →* B) ↔ γ.symm x ∈ π.ker :=
      Subgroup.mem_map_equiv
    rw [hm, MonoidHom.mem_ker, MonoidHom.mem_ker, ← hγ (γ.symm x),
      MulEquiv.apply_symm_apply]
  let e : B ⧸ π.ker ≃* Q := QuotientGroup.quotientKerEquivOfSurjective π hπ
  refine ⟨e.symm.trans ((QuotientGroup.congr π.ker π.ker γ hker).trans e), fun b => ?_⟩
  have hb : e (QuotientGroup.mk b) = π b := rfl
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, ← hb, MulEquiv.symm_apply_apply,
    QuotientGroup.congr_mk]
  rfl

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
