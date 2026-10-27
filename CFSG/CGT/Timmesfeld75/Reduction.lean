module

public import CFSG.CGT.Timmesfeld75.Defs
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models

public section

namespace CFSG.CGT.Timmesfeld75

@[expose] def Lemma213Stmt : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (T : Subgroup K), IsWC T → 4 ≤ Nat.card T →
    Subgroup.normalClosure (T : Set K) = ⊤ →
    (∀ R : Subgroup K, R.Normal → Group.IsSolvable R → R = ⊥) →
    ∃ N : Subgroup K, N.Normal ∧ N ≠ ⊥ ∧ IsSimpleGroup N ∧ N ⊓ T ≠ ⊥ ∧
      ∀ M : Subgroup K, M.Normal → M ≠ ⊥ → N ≤ M

@[expose] def Lemma215Stmt : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (T : Subgroup K), IsWC T → 4 ≤ Nat.card T →
    Subgroup.normalClosure (T : Set K) = ⊤ →
    (∀ R : Subgroup K, R.Normal → Group.IsSolvable R → R = ⊥) → IsSimpleGroup K

@[expose] def BenderSimpleInput : Prop :=
  ∀ (K : Type) [Group K], CFSG.BenderSuzuki.IsBenderGroup K → IsSimpleGroup K

end CFSG.CGT.Timmesfeld75
