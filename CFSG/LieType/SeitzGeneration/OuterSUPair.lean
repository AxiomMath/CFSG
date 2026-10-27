module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxUnitary

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.CTP

@[expose] def SubfieldPairSUOdd : Prop :=
  ∀ (ℓ f f₀ : ℕ) (K : Type) [Field K] (h : UnitaryFieldData ℓ f K) (k : Subfield K)
    (h₀ : UnitaryFieldData ℓ f₀ k) (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) (p : ℕ),
    p.Prime → p ≠ 2 → f = p * f₀ → ∀ n : ℕ, 3 ≤ n → ¬ (p ∣ n ∧ p ∣ ℓ ^ f₀ + 1) →
    ¬ (n = 3 ∧ ℓ ^ f₀ = 2) →
    ∀ A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      (suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom ≠ suSub h h₀ hbar n →
      Subgroup.closure ((suSub h h₀ hbar n : Set (gramSU h
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∪
        ((suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom : Set (gramSU h
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))) = ⊤

end CFSG.LieType.SeitzGeneration
