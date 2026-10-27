module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4MPts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def Sec4MRealizes (t : G) (φ : (Fin 7 → ZMod 2) → G) (m : G)
    (σ : Equiv.Perm (Option (Fin 7))) : Prop :=
  ∀ p : Option (Fin 7), m * sec4MPt t φ p * m⁻¹ = sec4MPt t φ (σ p)

variable {t : G} {φ : (Fin 7 → ZMod 2) → G} {m m₁ m₂ : G}
  {σ σ₁ σ₂ : Equiv.Perm (Option (Fin 7))}

theorem Sec4MRealizes.one : Sec4MRealizes t φ 1 1 := by
  intro p
  rw [one_mul, inv_one, mul_one]
  rfl

theorem Sec4MRealizes.mul (h₁ : Sec4MRealizes t φ m₁ σ₁) (h₂ : Sec4MRealizes t φ m₂ σ₂) :
    Sec4MRealizes t φ (m₁ * m₂) (σ₁ * σ₂) := by
  intro p
  calc (m₁ * m₂) * sec4MPt t φ p * (m₁ * m₂)⁻¹
      = m₁ * (m₂ * sec4MPt t φ p * m₂⁻¹) * m₁⁻¹ := by group
    _ = m₁ * sec4MPt t φ (σ₂ p) * m₁⁻¹ := by rw [h₂ p]
    _ = sec4MPt t φ (σ₁ (σ₂ p)) := h₁ (σ₂ p)
    _ = sec4MPt t φ ((σ₁ * σ₂) p) := by rfl

theorem Sec4MRealizes.unique (hinj : Function.Injective (sec4MPt t φ))
    (h₁ : Sec4MRealizes t φ m σ₁) (h₂ : Sec4MRealizes t φ m σ₂) : σ₁ = σ₂ := by
  apply Equiv.ext
  intro p
  exact hinj (by rw [← h₁ p, h₂ p])

theorem Sec4MRealizes.inv (h : Sec4MRealizes t φ m σ) : Sec4MRealizes t φ m⁻¹ σ⁻¹ := by
  intro p
  have hp : m * sec4MPt t φ (σ⁻¹ p) * m⁻¹ = sec4MPt t φ p := by
    simpa using h (σ⁻¹ p)
  rw [← hp]
  group

theorem Sec4MRealizes.sq_eq_one (hinj : Function.Injective (sec4MPt t φ))
    (h : Sec4MRealizes t φ m σ) (hm : m * m = 1) : σ * σ = 1 := by
  have h1 : Sec4MRealizes t φ (m * m) 1 := by
    rw [hm]
    exact Sec4MRealizes.one
  exact Sec4MRealizes.unique hinj (Sec4MRealizes.mul h h) h1

variable [Finite G] {L S : Subgroup G} {z : G} {A B : Subgroup G} {u : G}

end CFSG.OddStandard.SmallF3.Omega
