module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.S56

open Subgroup

theorem s3_three_cycle_of_ne_one :
    ∀ σ b : Equiv.Perm (Fin 3), σ ≠ 1 → b ^ 3 = 1 → b ≠ 1 →
      ∃ g₁ g₂ : Equiv.Perm (Fin 3),
        b = g₁ * σ * g₁⁻¹ ∨ b = (g₁ * σ * g₁⁻¹) * (g₂ * σ * g₂⁻¹) := by
  decide

theorem eq_of_normal_of_s3 {Γ : Type*} [Group Γ] {P H : Subgroup Γ} [P.Normal]
    (e : Γ ⧸ P ≃* Equiv.Perm (Fin 3)) (hPH : P ≤ H)
    (hH : ∀ g : Γ, ∀ h ∈ H, g * h * g⁻¹ ∈ H) {y : Γ} (hy3 : y ^ 3 ∈ P) (hyP : y ∉ P)
    (hyH : y ∉ H) : H = P := by
  refine le_antisymm (fun h hh => ?_) hPH
  by_contra hhP
  set f : Γ →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' P) with hf
  have hfs : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective P)
  have hker : ∀ x : Γ, f x = 1 ↔ x ∈ P := fun x => by
    rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hσ : f h ≠ 1 := fun h1 => hhP ((hker h).1 h1)
  have hb3 : (f y) ^ 3 = 1 := by rw [← map_pow]; exact (hker _).2 hy3
  have hb1 : f y ≠ 1 := fun h1 => hyP ((hker y).1 h1)
  obtain ⟨g₁, g₂, hg⟩ := s3_three_cycle_of_ne_one (f h) (f y) hσ hb3 hb1
  obtain ⟨γ₁, rfl⟩ := hfs g₁
  obtain ⟨γ₂, rfl⟩ := hfs g₂
  have hconj : ∀ γ : Γ, γ * h * γ⁻¹ ∈ H := fun γ => hH γ h hh
  have hyh : ∃ h' ∈ H, f y = f h' := by
    rcases hg with hg | hg
    · exact ⟨γ₁ * h * γ₁⁻¹, hconj γ₁, by rw [hg, map_mul, map_mul, map_inv]⟩
    · exact ⟨(γ₁ * h * γ₁⁻¹) * (γ₂ * h * γ₂⁻¹), mul_mem (hconj γ₁) (hconj γ₂), by
        rw [hg, map_mul, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]⟩
  obtain ⟨h', hh', hyf⟩ := hyh
  have hyP' : y * h'⁻¹ ∈ P := by
    rw [← hker, map_mul, map_inv, ← hyf, mul_inv_cancel]
  apply hyH
  have : y = (y * h'⁻¹) * h' := by group
  rw [this]
  exact mul_mem (hPH hyP') hh'

end CFSG.LocalAnalysis.EvenBN.Tits.S56
