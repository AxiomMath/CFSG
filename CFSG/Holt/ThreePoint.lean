module

public import CFSG.Holt.Fixed
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Holt

open MulAction CFSG.Open

variable {X : Type*} [Group X] {Ω : Type*} [MulAction X Ω]

section Triples

@[expose] def embFinThree {α β γ : Ω} (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ) : Fin 3 ↪ Ω :=
  ⟨![α, β, γ], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩

variable {α β γ : Ω} (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)

@[simp] theorem embFinThree_zero : embFinThree hαβ hαγ hβγ 0 = α := rfl

@[simp] theorem embFinThree_one : embFinThree hαβ hαγ hβγ 1 = β := rfl

@[simp] theorem embFinThree_two : embFinThree hαβ hαγ hβγ 2 = γ := rfl

end Triples

theorem isMultiplyPretransitive_three_iff :
    IsMultiplyPretransitive X Ω 3 ↔
      ∀ {α β γ α' β' γ' : Ω}, α ≠ β → α ≠ γ → β ≠ γ → α' ≠ β' → α' ≠ γ' → β' ≠ γ' →
        ∃ g : X, g • α = α' ∧ g • β = β' ∧ g • γ = γ' := by
  constructor
  · intro _ α β γ α' β' γ' h₁ h₂ h₃ h₁' h₂' h₃'
    obtain ⟨g, hg⟩ := exists_smul_eq X (embFinThree h₁ h₂ h₃) (embFinThree h₁' h₂' h₃')
    have e : ∀ i, g • embFinThree h₁ h₂ h₃ i = embFinThree h₁' h₂' h₃' i := fun i => by
      rw [← Function.Embedding.smul_apply, hg]
    exact ⟨g, e 0, e 1, e 2⟩
  · intro h
    refine ⟨fun a b => ?_⟩
    have hne : ∀ c : Fin 3 ↪ Ω, c 0 ≠ c 1 ∧ c 0 ≠ c 2 ∧ c 1 ≠ c 2 := fun c =>
      ⟨c.injective.ne (by decide), c.injective.ne (by decide), c.injective.ne (by decide)⟩
    obtain ⟨g, h0, h1, h2⟩ := h (hne a).1 (hne a).2.1 (hne a).2.2 (hne b).1 (hne b).2.1
      (hne b).2.2
    refine ⟨g, ?_⟩
    ext i
    rw [Function.Embedding.smul_apply]
    fin_cases i
    exacts [h0, h1, h2]

theorem isPretransitive_of_isMultiplyPretransitive_three [Finite Ω]
    [IsMultiplyPretransitive X Ω 3] (h3 : 3 ≤ Nat.card Ω) : IsPretransitive X Ω :=
  is_one_pretransitive_iff.mp (isMultiplyPretransitive_of_le (by norm_num) h3)

end CFSG.Holt
