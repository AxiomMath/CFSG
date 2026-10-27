module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

@[expose] def rootGroup (X : Type*) [Group X] (t : X) : Subgroup X :=
  closure {x : X | x * x = t}

structure RootFactsFor (X : Type*) [Group X] (t : X) : Prop where
  card_cent : Nat.card ↥(centralizer ({t} : Set X)) = 1920
  roots_le : Set.ncard {x : X | x * x = t} ≤ 20
  card_E : Nat.card ↥(rootGroup X t) = 32
  cent_E : ∀ l : X, (∀ r : X, r * r = t → l * r = r * l) → l = 1 ∨ l = t
  beta : ∃ β : X, β * t = t * β ∧ orderOf β = 3 ∧
    Nat.card ↥(rootGroup X t ⊓ centralizer ({β} : Set X)) = 8 ∧
    ∃ d₁ ∈ rootGroup X t ⊓ centralizer ({β} : Set X),
      ∃ d₂ ∈ rootGroup X t ⊓ centralizer ({β} : Set X), d₁ * d₂ ≠ d₂ * d₁

@[expose] def RootFactsClass (X : Type*) [Group X] : Prop :=
  ∀ t : X, orderOf t = 2 → (∃ g : X, g * g = t) → RootFactsFor X t

theorem RootFactsFor.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {t : X}
    (h : RootFactsFor X t) : RootFactsFor Y (e t) := by
  have hroots : {y : Y | y * y = e t} = e '' {x : X | x * x = t} := by
    ext y
    constructor
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hy
    · rintro ⟨x, hx, rfl⟩
      simp only [Set.mem_ofPred_eq, ← map_mul]
      exact congrArg e hx
  have hE : rootGroup Y (e t) = (rootGroup X t).map e.toMonoidHom := by
    unfold rootGroup
    rw [hroots, MonoidHom.map_closure]
    rfl
  have hcent : centralizer ({e t} : Set Y) = (centralizer ({t} : Set X)).map e.toMonoidHom := by
    ext y
    simp only [Subgroup.mem_map, mem_centralizer_singleton_iff]
    constructor
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hy
    · rintro ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
      exact congrArg e hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcent, Nat.card_congr ((centralizer ({t} : Set X)).equivMapOfInjective e.toMonoidHom
      e.injective).toEquiv.symm]
    exact h.card_cent
  · rw [hroots, Set.ncard_image_of_injective _ e.injective]
    exact h.roots_le
  · rw [hE, Nat.card_congr ((rootGroup X t).equivMapOfInjective e.toMonoidHom
      e.injective).toEquiv.symm]
    exact h.card_E
  · intro l hl
    have := h.cent_E (e.symm l) (fun r hr => by
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hl (e r) (by rw [← map_mul, hr]))
    rcases this with h1 | h1
    · left; simpa using congrArg e h1
    · right; simpa using congrArg e h1
  · obtain ⟨β, hβt, hβ3, hcard, d₁, hd₁, d₂, hd₂, hne⟩ := h.beta
    have himg : rootGroup Y (e t) ⊓ centralizer ({e β} : Set Y) =
        (rootGroup X t ⊓ centralizer ({β} : Set X)).map e.toMonoidHom := by
      rw [hE, Subgroup.map_inf _ _ _ e.injective]
      congr 1
      ext y
      simp only [Subgroup.mem_map, mem_centralizer_singleton_iff]
      constructor
      · intro hy
        refine ⟨e.symm y, ?_, by simp⟩
        apply e.injective
        simp only [map_mul, MulEquiv.apply_symm_apply]
        exact hy
      · rintro ⟨x, hx, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
        exact congrArg e hx
    refine ⟨e β, ?_, ?_, ?_, e d₁, ?_, e d₂, ?_, ?_⟩
    · rw [← map_mul, ← map_mul, hβt]
    · rw [MulEquiv.orderOf_eq]; exact hβ3
    · rw [himg, Nat.card_congr ((rootGroup X t ⊓ centralizer ({β} : Set X)).equivMapOfInjective
        e.toMonoidHom e.injective).toEquiv.symm]
      exact hcard
    · rw [himg]; exact ⟨d₁, hd₁, rfl⟩
    · rw [himg]; exact ⟨d₂, hd₂, rfl⟩
    · intro hc
      apply hne
      apply e.injective
      simp only [map_mul]
      exact hc

theorem RootFactsFor.conj {X : Type*} [Group X] {t : X} (h : RootFactsFor X t) (g : X) :
    RootFactsFor X (g * t * g⁻¹) := by
  have := h.of_mulEquiv (MulAut.conj g)
  simpa [MulAut.conj_apply] using this

theorem RootFactsClass.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : RootFactsClass X) : RootFactsClass Y := by
  intro t ht2 ⟨g, hg⟩
  have := (h (e.symm t) (by rw [MulEquiv.orderOf_eq]; exact ht2)
    ⟨e.symm g, by rw [← map_mul, hg]⟩).of_mulEquiv e
  simpa using this

theorem RootFactsClass.of_class {X : Type*} [Group X] (t₀ : X) (h₀ : RootFactsFor X t₀)
    (hcls : ∀ t : X, orderOf t = 2 → (∃ g : X, g * g = t) → ∃ g : X, t = g * t₀ * g⁻¹) :
    RootFactsClass X := by
  intro t ht2 hsq
  obtain ⟨g, rfl⟩ := hcls t ht2 hsq
  exact h₀.conj g

end CFSG.EvenSporadicStandard.Fin76b
