module

public import CFSG.LieType.SeitzGeneration.SubfieldPairSUOddProof
public import CFSG.RankThree.PartOne.SEITZ5.UPair

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration.SUPair CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.Unitary

theorem subfieldPairSUOdd_of_not_three_two (ℓ f f₀ : ℕ) (K : Type)
    [Field K] (h : UnitaryFieldData ℓ f K) (k : Subfield K) (h₀ : UnitaryFieldData ℓ f₀ k)
    (hbar : ∀ c : k, (h₀.bar c : K) = h.bar c) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : f = p * f₀) (n : ℕ) (hn : 3 ≤ n) (hnq : ¬(n = 3 ∧ ℓ ^ f₀ = 2))
    (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hne : (suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom ≠ suSub h h₀ hbar n) :
    Subgroup.closure ((suSub h h₀ hbar n : Set (gramSU h
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∪
      ((suSub h h₀ hbar n).map (primeFormConjSU h _ A).toMonoidHom : Set (gramSU h
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))) = ⊤ := by
  classical
  by_cases hq : ℓ ^ f₀ = 2
  · have hn4 : 4 ≤ n := by
      by_contra h4
      exact hnq ⟨by omega, hq⟩
    obtain ⟨hℓ2, hf₀1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 hq
    subst hℓ2
    exact CFSG.RankThree.PartOne.SEITZ5.subfieldPairSUF2Odd_of_four_le hn4 f f₀ K h k h₀ hbar p hp hp2
      hf hf₀1 A hne
  · exact subfieldPairSUOdd_of_ne_two ℓ f f₀ K h k h₀ hbar p hp hp2 hf hq n hn A hne

end CFSG.LieType.SeitzGeneration
