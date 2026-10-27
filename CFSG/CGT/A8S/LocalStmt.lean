module

public import CFSG.CGT.A8S.Stmt
public import CFSG.Holt.General.Defs

public section

namespace CFSG.CGT.A8S

open CFSG.CGT.Timmesfeld75

structure A8Hyp {G : Type} [Group G] (T H : Subgroup G) : Prop where
  le : T ≤ H
  wc : IsWC T
  nat : NaturalSL T H 3 1
  compl : ∃ K : Subgroup G, K ≤ H ∧ T ⊓ K = ⊥ ∧ T ⊔ K = H
  odd : Odd H.index

@[expose] def CoreStatementA8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ T H : Subgroup G, A8Hyp T H →
      Subgroup.centralizer (T : Set G) = T ∨ Nonempty (G ≃* alternatingGroup (Fin 9))

@[expose] def PairStatementA8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ T H : Subgroup G, A8Hyp T H → Subgroup.centralizer (T : Set G) = T →
      ∃ T₁ : Subgroup G, A8CtxHyp T T₁

@[expose] def HoltA9Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (M : Subgroup G), M ≠ ⊤ →
    ∀ (S : Sylow 2 G) (z : G), Nat.card S = 2 ^ 6 →
      (∀ x ∈ (S : Subgroup G), ((∀ y ∈ (S : Subgroup G), x * y = y * x) ↔ (x = 1 ∨ x = z))) →
      CFSG.Holt.General.IsHoltTriple G (G ⧸ M) z ((1 : G) : G ⧸ M) →
        M.index = 9 ∧ Nonempty (G ≃* alternatingGroup (Fin 9))

end CFSG.CGT.A8S
