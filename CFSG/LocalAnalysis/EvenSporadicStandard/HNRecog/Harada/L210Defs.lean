module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

variable {X : Type} [Group X]

structure GoldHyp (T : Sylow 2 X) (A : Subgroup X) : Prop where
  le : A ≤ (T : Subgroup X)
  elemAb : IsElemAbelian 2 A
  weak : ∀ g : X, (∀ a ∈ A, g * a * g⁻¹ ∈ (T : Subgroup X)) → ∀ a ∈ A, g * a * g⁻¹ ∈ A

structure L210Hyp (A : Subgroup X) : Prop where
  elemAb : IsElemAbelian 2 A
  card : Nat.card A = 2 ^ 8
  centralizer_le : ∀ i ∈ normalizer (A : Set X), i ∉ A → i * i = 1 →
    Nat.card ↥(A ⊓ centralizer ({i} : Set X)) ≤ 16
  noE16 : ∀ D : Subgroup X, D ≤ normalizer (A : Set X) → IsElemAbelian 2 D → D ⊓ A = ⊥ →
    Nat.card D ≤ 8

end CFSG.EvenSporadicStandard.HNRecog.Harada
