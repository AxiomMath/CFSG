module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataReindex
public import CFSG.LieType.Universal.Spin.Forms

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CFSG.LieType.Universal.Spin

@[expose] def plusIndexEquiv (n : ℕ) : (Fin n ⊕ Fin n) ≃ Fin (2 * n) :=
  Fintype.equivFinOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)

@[expose] def oddIndexEquiv (n : ℕ) : (Fin n ⊕ Fin n ⊕ Unit) ≃ Fin (2 * n + 1) :=
  Fintype.equivFinOfCardEq (by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    omega)

@[expose] def minusIndexEquiv (n : ℕ) (hn : 1 ≤ n) :
    (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) ≃ Fin (2 * n) :=
  Fintype.equivFinOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)

variable (n : ℕ) (K : Type*) [Field K]

@[expose] def coordinateQuadPlus : QuadraticForm K (Fin (2 * n) → K) :=
  reindexQuadraticForm (plusIndexEquiv n) (quadPlus n K)

@[expose] def coordinateQuadOdd : QuadraticForm K (Fin (2 * n + 1) → K) :=
  reindexQuadraticForm (oddIndexEquiv n) (quadOdd n K)

@[expose] def coordinateQuadMinus (hn : 1 ≤ n) (b c : K) :
    QuadraticForm K (Fin (2 * n) → K) :=
  reindexQuadraticForm (minusIndexEquiv n hn) (quadMinus n K b c)

theorem coordinateQuadPlus_apply (v : Fin (2 * n) → K) :
    coordinateQuadPlus n K v =
      ∑ i, v (plusIndexEquiv n (.inl i)) * v (plusIndexEquiv n (.inr i)) := by
  rw [coordinateQuadPlus, reindexQuadraticForm_apply, quadPlus_apply]

theorem coordinateQuadOdd_apply (v : Fin (2 * n + 1) → K) :
    coordinateQuadOdd n K v =
      ∑ i, v (oddIndexEquiv n (.inl i)) * v (oddIndexEquiv n (.inr (.inl i))) +
        v (oddIndexEquiv n (.inr (.inr ()))) ^ 2 := by
  rw [coordinateQuadOdd, reindexQuadraticForm_apply, quadOdd_apply]

theorem coordinateQuadMinus_apply (hn : 1 ≤ n) (b c : K) (v : Fin (2 * n) → K) :
    coordinateQuadMinus n K hn b c v =
      ∑ i, v (minusIndexEquiv n hn (.inl i)) *
        v (minusIndexEquiv n hn (.inr (.inl i))) +
        v (minusIndexEquiv n hn (.inr (.inr 0))) ^ 2 +
        b * v (minusIndexEquiv n hn (.inr (.inr 0))) *
          v (minusIndexEquiv n hn (.inr (.inr 1))) +
        c * v (minusIndexEquiv n hn (.inr (.inr 1))) ^ 2 := by
  rw [coordinateQuadMinus, reindexQuadraticForm_apply, quadMinus_apply]

@[expose] def coordinatePlusIsometry : (quadPlus n K).IsometryEquiv (coordinateQuadPlus n K) :=
  reindexQuadraticIsometry (plusIndexEquiv n) (quadPlus n K)

@[expose] def coordinateOddIsometry : (quadOdd n K).IsometryEquiv (coordinateQuadOdd n K) :=
  reindexQuadraticIsometry (oddIndexEquiv n) (quadOdd n K)

@[expose] def coordinateMinusIsometry (hn : 1 ≤ n) (b c : K) :
    (quadMinus n K b c).IsometryEquiv (coordinateQuadMinus n K hn b c) :=
  reindexQuadraticIsometry (minusIndexEquiv n hn) (quadMinus n K b c)

end CFSG.ComponentClassification.CatalogueBOrthogonalPointData
