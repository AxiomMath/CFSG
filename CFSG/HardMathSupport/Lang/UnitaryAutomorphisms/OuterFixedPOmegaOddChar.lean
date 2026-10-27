module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaCount
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaOrder
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPOmegaSwap

public section

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.ComponentClassification.CatLeaf
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCOrthogonalSubfield

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

variable {K : Type} [Field K] [Finite K] (k : Subfield K) (n : ℕ)

private theorem finite_subfield : Finite k := Finite.of_injective (algebraMap k K)
  (algebraMap k K).injective

theorem card_subfieldFixedGroup_odd_dvd (hn : 1 ≤ n) (h2 : (2 : k) ≠ 0)
    (Q : QuadraticForm K (Fin (2 * n + 1) → K)) :
    Nat.card (subfieldFixedGroup k (coordinateQuadOdd n k) Q) ∣
      lieOrderNumerator .POmegaOdd n (Nat.card k) := by
  have := finite_subfield k
  obtain ⟨g, hg⟩ := exists_det_neg_one_of_swap (coordinateQuadOdd n k)
    ((oddIndexEquiv n).injective.ne (by simp) : oddIndexEquiv n (.inl ⟨0, hn⟩) ≠
      oddIndexEquiv n (.inr (.inl ⟨0, hn⟩))) (coordinateQuadOdd_swap n hn)
  have h := two_mul_card_subfieldFixedGroup_dvd k (coordinateQuadOdd n k) Q g hg h2
  rw [card_matrixIsometries_coordinateQuadOdd h2] at h
  exact Nat.dvd_of_mul_dvd_mul_left two_pos h

theorem card_subfieldFixedGroup_plus_dvd (hn : 1 ≤ n) (h2 : (2 : k) ≠ 0)
    (Q : QuadraticForm K (Fin (2 * n) → K)) :
    Nat.card (subfieldFixedGroup k (coordinateQuadPlus n k) Q) ∣
      lieOrderNumerator .POmegaPlus n (Nat.card k) := by
  have := finite_subfield k
  obtain ⟨g, hg⟩ := exists_det_neg_one_of_swap (coordinateQuadPlus n k)
    ((plusIndexEquiv n).injective.ne (by simp) : plusIndexEquiv n (.inl ⟨0, hn⟩) ≠
      plusIndexEquiv n (.inr ⟨0, hn⟩)) (coordinateQuadPlus_swap n hn)
  have h := two_mul_card_subfieldFixedGroup_dvd k (coordinateQuadPlus n k) Q g hg h2
  rw [card_matrixIsometries_coordinateQuadPlus h2 n hn] at h
  exact Nat.dvd_of_mul_dvd_mul_left two_pos h

theorem card_subfieldFixedGroup_minus_dvd (hn : 2 ≤ n) (h2 : (2 : k) ≠ 0) {b c : k}
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    (Q : QuadraticForm K (Fin (2 * n) → K)) :
    Nat.card (subfieldFixedGroup k (coordinateQuadMinus n k (by omega) b c) Q) ∣
      lieOrderNumerator .POmegaMinus n (Nat.card k) := by
  have := finite_subfield k
  have hn1 : 0 < n - 1 := by omega
  obtain ⟨g, hg⟩ := exists_det_neg_one_of_swap (coordinateQuadMinus n k (by omega) b c)
    ((minusIndexEquiv n (by omega)).injective.ne (by simp) :
      minusIndexEquiv n (by omega) (.inl ⟨0, hn1⟩) ≠
      minusIndexEquiv n (by omega) (.inr (.inl ⟨0, hn1⟩)))
    (coordinateQuadMinus_swap n (by omega) hn1 b c)
  have h := two_mul_card_subfieldFixedGroup_dvd k (coordinateQuadMinus n k (by omega) b c) Q g hg h2
  rw [card_matrixIsometries_coordinateQuadMinus h2 n (by omega) hirr] at h
  exact Nat.dvd_of_mul_dvd_mul_left two_pos h

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
