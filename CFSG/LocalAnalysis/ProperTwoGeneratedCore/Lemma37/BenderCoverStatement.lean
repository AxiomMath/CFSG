module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

@[expose] def BenderCoverStatement : Prop :=
  ∀ (J : Type) [Group J] [Finite J], commutator J = ⊤ → Nat.card (Subgroup.center J) = 2 →
    CFSG.BenderSuzuki.IsBenderGroup (J ⧸ Subgroup.center J) →
    Nonempty ((J ⧸ Subgroup.center J) ≃* CFSG.Theory.Comparator.PSL2Model 2) ∨
    Nonempty ((J ⧸ Subgroup.center J) ≃* ↥(CFSG.Theory.Comparator.SzModel 1))

@[expose] def RankTwoCoverStatement : Prop :=
  ∀ (J : Type) [Group J] [Finite J], commutator J = ⊤ → IsPGroup 2 (Subgroup.center J) →
    Subgroup.center J ≠ ⊥ → IsCyclic (Subgroup.center J) →
    IsSimpleGroup (J ⧸ Subgroup.center J) →
    CFSG.Assembly.twoRank (J ⧸ Subgroup.center J) = 2 →
    ∀ x y : J, orderOf x = 2 → orderOf y = 2 → x = y

end CFSG.ProperTwoGeneratedCore.Lemma37
