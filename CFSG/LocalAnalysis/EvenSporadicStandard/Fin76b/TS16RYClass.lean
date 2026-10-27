module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RY0B

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

@[expose] def S16ModelClass (X : Type*) [Group X] : Prop :=
  ∀ t β : X, orderOf t = 2 → (∃ g : X, g * g = t) → β ∈ centralizer ({t} : Set X) →
    orderOf β = 3 → S16Model X t β

theorem S16ModelClass.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : S16ModelClass X) : S16ModelClass Y := by
  intro t β ht2 hsq hβt hβ3
  obtain ⟨g, hg⟩ := hsq
  have hβt' : e.symm β ∈ centralizer ({e.symm t} : Set X) := by
    rw [mem_centralizer_singleton_iff] at hβt ⊢
    rw [← map_mul, ← map_mul, hβt]
  have := (h (e.symm t) (e.symm β) (by rw [MulEquiv.orderOf_eq]; exact ht2)
    ⟨e.symm g, by rw [← map_mul, hg]⟩ hβt' (by rw [MulEquiv.orderOf_eq]; exact hβ3)).of_mulEquiv e
  simpa using this

theorem S16ModelClass.of_class {X : Type*} [Group X] [Finite X] {t₀ β₀ : X}
    (h₀ : S16Model X t₀ β₀)
    (hcls : ∀ t : X, orderOf t = 2 → (∃ g : X, g * g = t) → ∃ g : X, t = g * t₀ * g⁻¹)
    (hcard : Nat.card ↥(centralizer ({t₀} : Set X)) = 1920)
    (hβ₀ : β₀ ∈ centralizer ({t₀} : Set X)) (hβ₀3 : orderOf β₀ = 3) : S16ModelClass X :=
  fun t β ht2 hsq hβt hβ3 => h₀.of_class hcls hcard hβ₀ hβ₀3 t β ht2 hsq hβt hβ3

end CFSG.EvenSporadicStandard.Fin76b
