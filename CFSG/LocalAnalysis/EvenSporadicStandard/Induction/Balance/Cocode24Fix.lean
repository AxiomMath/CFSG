module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Act

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

open Equiv

theorem card_syn : Nat.card Syn = 2 ^ 12 := by
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

@[expose] def fixSyn (B : Subgroup (Perm (Fin 24))) : Set Syn := {s | ∀ b ∈ B, act b s = s}

@[expose] def OffenderBound (S : Subgroup (Perm (Fin 24))) : Prop :=
  ∀ B : Subgroup (Perm (Fin 24)), B ≤ S → (∀ b ∈ B, b * b = 1) →
    (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) → B ≠ ⊥ → Nat.card B * Nat.card (fixSyn B) ≤ 2 ^ 11

@[expose] def SylowFacts : Prop :=
  ∃ S : Subgroup (Perm (Fin 24)), S ≤ aut ∧ Nat.card S = 2 ^ 10 ∧ OffenderBound S

end CFSG.EvenSporadicStandard.Induction.Balance.Cocode24
