module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueLin

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

@[expose] def axSet (ms : Array (Array ℕ)) : Set (Fin 1024 → Fin 1024) :=
  {f | ∃ k < ms.size, f = fn ms[k]!}

@[expose] def axQ (ms : Array (Array ℕ)) (q : ℕ → Bool) : Set (Fin 1024 → Fin 1024) :=
  {f | ∃ k < ms.size, q k = true ∧ f = fn ms[k]!}

@[expose] def axSpec (ms : Array (Array ℕ)) (q : ℕ → Bool) : Prop :=
  ∀ X : Finset (Fin 1024 → Fin 1024), (X : Set (Fin 1024 → Fin 1024)) ⊆ axSet ms →
    (∀ x ∈ X, ∀ y ∈ X, x ∘ y ∈ X) → (∀ x ∈ X, x ∘ x = id) → X.Nonempty →
    (∀ x ∈ X, x ∈ axQ ms q) ∨ X.card * (fixSet X).card ≤ 2 ^ 8

end CFSG.EvenSporadicStandard.TwoFi22.DS81
