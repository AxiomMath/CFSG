module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

@[expose] def Harada75E8 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsPGroup 2 S →
    ∀ A : Subgroup S, IsElemAbelian 2 A → Nat.card A = 8 →
      Subgroup.centralizer (A : Set S) ≤ A →
        ∀ U : Subgroup S, ∃ X : Finset S, X.card ≤ 4 ∧ Subgroup.closure (X : Set S) = U

end CFSG.EvenSporadicStandard.Fin76b
