module

public import CFSG.CGT.Timmesfeld75.Form2

public section

namespace CFSG.LargeExtraspecial.S4

open CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank

@[expose] def Form2StrongConclusion (K : Type) [Group K] (T : Subgroup K) : Prop :=
  (Nat.card T ≤ 2 ∧ ZStarCase K) ∨
    (4 ≤ Nat.card T ∧ commutator K = ⊤ ∧ Odd (Nat.card (Subgroup.center K)) ∧
      IsSimpleGroup (K ⧸ Subgroup.center K) ∧
      StdPair (K ⧸ Subgroup.center K) (T.map (QuotientGroup.mk' (Subgroup.center K))))

@[expose] def Form2StrongStmt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L : Subgroup X), IsWC L →
    Form2StrongConclusion (Form2Q X L) (Form2L X L)

@[expose] def BenderConjCountInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ f : ℕ, StatedClassicalModel G .PSL 2 2 f → 2 ^ f + 1 ≤ Nat.card (Sylow 2 G)) ∧
    (∀ s : ℕ, Odd s → 3 ≤ s → CFSG.Blueprint.LieModel G .twistedB2 0 2 s →
      2 ^ (2 * s) + 1 ≤ Nat.card (Sylow 2 G)) ∧
    (∀ s : ℕ, 2 ≤ s → StatedClassicalModel G .PSU 3 2 s →
      2 ^ (3 * s) + 1 ≤ Nat.card (Sylow 2 G))

end CFSG.LargeExtraspecial.S4
