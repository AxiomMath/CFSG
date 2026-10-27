module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG

public section

namespace CFSG.Goldschmidt

@[expose] def S_GSz8Mult : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    Nonempty (K ⧸ Subgroup.center K ≃* CFSG.Open.Sz 1) → Nat.card (Subgroup.center K) ≤ 4

@[expose] def S_G32Q : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → IsGoldTypeI L →
    IsPGroup 2 (Subgroup.center L) → ∀ A : Subgroup L, IsSStarIn ⊤ A → ∀ T : Sylow 2 L,
    A ≤ T → ∀ a ∈ A, a ∉ Subgroup.center L →
    (∀ M : Subgroup L, Subgroup.centralizer ({a} : Set L) ≤ M → M ≠ ⊤ →
      M ≤ Subgroup.normalizer ((T : Subgroup L) : Set L)) ∧
    Subgroup.normalizer ((T : Subgroup L) : Set L) ⊓
      Subgroup.centralizer
        (((T : Subgroup L) ⊓ Subgroup.centralizer ({a} : Set L) : Subgroup L) : Set L) ≤ T

end CFSG.Goldschmidt
