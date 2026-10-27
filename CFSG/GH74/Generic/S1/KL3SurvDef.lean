module

public import CFSG.GH74.Generic.S1.KL3Red

public section

open Subgroup CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

@[expose] def KL3SurvL4 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], LieModel S .PSL 4 3 1 →
    ∀ (F : Type) [Field F] [Finite F], Nat.card F = 3 →
      ∀ Pb : Subgroup S, Nonempty (↥Pb ≃* SL(3, F)) →
        (∀ α : MulAut S, Odd (orderOf α) → (∀ p ∈ Pb, α p = p) → α = 1) ∧
          ∃ E : Subgroup S, CFSG.Open.IsElemAbelian 2 E ∧ 4 < Nat.card E

@[expose] def KL3SurvG2 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], LieModel S .G2 0 3 1 →
    ∀ (F : Type) [Field F] [Finite F], Nat.card F = 3 →
      ∀ Pb : Subgroup S, Nonempty (↥Pb ≃* SL(3, F)) →
        (∀ α : MulAut S, Odd (orderOf α) → (∀ p ∈ Pb, α p = p) → α = 1) ∧
          ∃ E : Subgroup S, CFSG.Open.IsElemAbelian 2 E ∧ 4 < Nat.card E

theorem kl3Surv_of_parts (h4 : KL3SurvL4) (h2 : KL3SurvG2) : KL3Surv := by
  intro S _ _ hS F _ _ hF Pb hPb
  rcases hS with hS | hS
  · exact h4 S hS F hF Pb hPb
  · exact h2 S hS F hF Pb hPb

end CFSG.GH74.Generic.S1
