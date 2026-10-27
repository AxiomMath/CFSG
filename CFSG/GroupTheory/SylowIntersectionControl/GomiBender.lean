module

public import CFSG.Open.FusionDefs

public section

namespace CFSG.GroupTheory

@[expose] def GomiBender : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (H : Subgroup X), CFSG.Open.fusionStronglyEmbedded H →
    (∀ S : Sylow 2 X, IsCyclic (S : Subgroup X) ∨
      ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2)))) ∨
    ∃ (M N : Subgroup X) (_ : M.Normal) (_ : N.Normal) (_ : (M.subgroupOf N).Normal),
      M ≤ N ∧ Odd (Nat.card M) ∧ Odd N.index ∧
        CFSG.Open.fusionIsBenderGroup (N ⧸ M.subgroupOf N)

end CFSG.GroupTheory
