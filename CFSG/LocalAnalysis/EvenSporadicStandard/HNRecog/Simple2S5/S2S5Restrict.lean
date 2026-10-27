module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

variable {G α β : Type*} [Group G] [MulAction G α]

@[expose] def stabEmb (ι : β → α) : Subgroup G where
  carrier := {g | ∃ τ : Equiv.Perm β, ∀ b, g • ι b = ι (τ b)}
  mul_mem' := by
    rintro g h ⟨τ₁, h₁⟩ ⟨τ₂, h₂⟩
    refine ⟨τ₁ * τ₂, fun b => ?_⟩
    calc (g * h) • ι b = g • (h • ι b) := mul_smul g h (ι b)
      _ = g • ι (τ₂ b) := by rw [h₂ b]
      _ = ι (τ₁ (τ₂ b)) := h₁ (τ₂ b)
      _ = ι ((τ₁ * τ₂) b) := by rw [Equiv.Perm.mul_apply]
  one_mem' := by
    refine ⟨1, fun b => ?_⟩
    rw [one_smul]
    rfl
  inv_mem' := by
    rintro g ⟨τ, h⟩
    refine ⟨τ⁻¹, fun b => ?_⟩
    rw [inv_smul_eq_iff, h (τ⁻¹ b)]
    simp

theorem mem_stabEmb {ι : β → α} {g : G} :
    g ∈ stabEmb ι ↔ ∃ τ : Equiv.Perm β, ∀ b, g • ι b = ι (τ b) :=
  Iff.rfl

theorem exists_restrictHom (ι : β → α) (hι : Function.Injective ι) :
    ∃ ρ : stabEmb (G := G) ι →* Equiv.Perm β, ∀ (g : stabEmb (G := G) ι) (b : β),
      (g : G) • ι b = ι (ρ g b) := by
  let τ : stabEmb (G := G) ι → Equiv.Perm β := fun g => Classical.choose g.2
  have hτ : ∀ (g : stabEmb (G := G) ι) (b : β), (g : G) • ι b = ι (τ g b) :=
    fun g => Classical.choose_spec g.2
  have huniq : ∀ (g : stabEmb (G := G) ι) (σ σ' : Equiv.Perm β),
      (∀ b, (g : G) • ι b = ι (σ b)) →
      (∀ b, (g : G) • ι b = ι (σ' b)) → σ = σ' := by
    intro g σ σ' hσ hσ'
    ext b
    exact hι (by rw [← hσ b, hσ' b])
  refine ⟨MonoidHom.mk' τ ?_, fun g b => hτ g b⟩
  intro g h
  apply huniq (g * h) (τ (g * h)) (τ g * τ h)
  · intro b
    exact hτ (g * h) b
  · intro b
    show ((g : G) * (h : G)) • ι b = ι ((τ g * τ h) b)
    rw [mul_smul, hτ h b, hτ g (τ h b), Equiv.Perm.mul_apply]

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5

end
