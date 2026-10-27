module

public import Mathlib.GroupTheory.GroupAction.ConjAct

public section

namespace CFSG.EvenSporadicStandard.HSStd.HL34

open Subgroup

variable {D : Type*} [Group D] (H : Subgroup D) [H.Normal] {A : Type*} [Group A] (ψ : ↥H ≃* A)

@[expose] def actionHom : D →* MulAut A :=
  (MulAut.congr ψ).toMonoidHom.comp MulAut.conjNormal

theorem actionHom_apply (d : D) (h : H) :
    actionHom H ψ d (ψ h) = ψ (MulAut.conjNormal d h) := by
  show ψ (MulAut.conjNormal d (ψ.symm (ψ h))) = _
  rw [ψ.symm_apply_apply]

theorem actionHom_eq_one_iff (d : D) : actionHom H ψ d = 1 ↔ d ∈ centralizer (H : Set D) := by
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro x hx
    have h1 : ψ (MulAut.conjNormal d ⟨x, hx⟩) = ψ ⟨x, hx⟩ := by
      rw [← actionHom_apply, h]
      rfl
    have h2 := congrArg Subtype.val (ψ.injective h1)
    rw [MulAut.conjNormal_apply] at h2
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  · intro h
    refine MulEquiv.ext fun a => ?_
    obtain ⟨x, rfl⟩ := ψ.surjective a
    rw [actionHom_apply]
    refine congrArg ψ (Subtype.ext ?_)
    rw [MulAut.conjNormal_apply]
    exact mul_inv_eq_iff_eq_mul.2 (mem_centralizer_iff.1 h x x.2).symm

variable {R : Type*} [Group R] (e : R ≃* MulAut A)

@[expose] def rho : D →* R := (e.symm : MulAut A ≃* R).toMonoidHom.comp (actionHom H ψ)

theorem rho_apply (d : D) (h : H) : e (rho H ψ e d) (ψ h) = ψ (MulAut.conjNormal d h) := by
  rw [rho, MonoidHom.comp_apply]
  exact (congrArg (fun f : MulAut A => f (ψ h)) (e.apply_symm_apply (actionHom H ψ d))).trans
    (actionHom_apply H ψ d h)

theorem rho_eq_one_iff (d : D) : rho H ψ e d = 1 ↔ d ∈ centralizer (H : Set D) := by
  rw [← actionHom_eq_one_iff H ψ d, rho, MonoidHom.comp_apply]
  exact ⟨fun h => by simpa using congrArg e h, fun h => by simp [h]⟩

theorem rho_injective (h : centralizer (H : Set D) = ⊥) : Function.Injective (rho H ψ e) := by
  rw [injective_iff_map_eq_one]
  intro d hd
  have := (rho_eq_one_iff H ψ e d).1 hd
  rw [h, mem_bot] at this
  exact this

end CFSG.EvenSporadicStandard.HSStd.HL34
