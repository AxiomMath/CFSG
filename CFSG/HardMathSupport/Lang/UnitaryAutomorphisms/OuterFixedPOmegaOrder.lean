module

public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.ComponentClassification.CatLeaf
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

variable {F : Type} [Field F] [Finite F]

private theorem cast_prod_sub_one (q a b s : ℕ) (hq : 1 ≤ q) :
    ((∏ i ∈ Finset.Icc a b, (q ^ (s * i) - 1) : ℕ) : ℤ) =
      ∏ i ∈ Finset.Icc a b, ((q : ℤ) ^ (s * i) - 1) := by
  push_cast
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
  push_cast
  rfl

theorem card_matrixIsometries_coordinateQuadOdd (h2 : (2 : F) ≠ 0) (n : ℕ) :
    Nat.card (matrixIsometries (coordinateQuadOdd n F)) =
      2 * lieOrderNumerator .POmegaOdd n (Nat.card F) := by
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have h1 : Nat.card (matrixIsometries (coordinateQuadOdd n F)) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadOdd n F)) :=
    Nat.card_congr (CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter.matrixIsometriesReindexEquiv
      (oddIndexEquiv n) (quadOdd n F)).toEquiv
  rw [h1]
  have h3 := CFSG.ClassicalInvolution.card_orthogonalGroup_quadOdd_of_two_ne_zero h2 n
  have h4 := cast_prod_sub_one (Nat.card F) 1 n 2 hq
  apply Nat.cast_injective (R := ℤ)
  rw [h3]
  simp only [lieOrderNumerator]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, h4]
  push_cast
  ring

theorem card_matrixIsometries_coordinateQuadPlus (h2 : (2 : F) ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (matrixIsometries (coordinateQuadPlus n F)) =
      2 * lieOrderNumerator .POmegaPlus n (Nat.card F) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have h1 : Nat.card (matrixIsometries (coordinateQuadPlus (m + 1) F)) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus (m + 1) F)) :=
    Nat.card_congr (CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter.matrixIsometriesReindexEquiv
      (plusIndexEquiv (m + 1)) (quadPlus (m + 1) F)).toEquiv
  rw [h1]
  have h3 := CFSG.ClassicalInvolution.card_orthogonalGroup_quadPlus_of_two_ne_zero h2 m
  have h4 := cast_prod_sub_one (Nat.card F) 1 m 2 hq
  have h5 : ((Nat.card F ^ (m + 1) - 1 : ℕ) : ℤ) = (Nat.card F : ℤ) ^ (m + 1) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
    push_cast
    rfl
  apply Nat.cast_injective (R := ℤ)
  rw [h3]
  simp only [lieOrderNumerator, Nat.add_sub_cancel]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, h4, h5]
  push_cast
  ring

theorem card_matrixIsometries_coordinateQuadMinus (h2 : (2 : F) ≠ 0) (n : ℕ) (hn : 1 ≤ n)
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (matrixIsometries (coordinateQuadMinus n F hn b c)) =
      2 * lieOrderNumerator .POmegaMinus n (Nat.card F) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have h1 : Nat.card (matrixIsometries (coordinateQuadMinus (m + 1) F hn b c)) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus (m + 1) F b c)) :=
    Nat.card_congr (CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter.matrixIsometriesReindexEquiv
      (minusIndexEquiv (m + 1) hn) (quadMinus (m + 1) F b c)).toEquiv
  rw [h1]
  have h3 := CFSG.ClassicalInvolution.card_orthogonalGroup_quadMinus_of_two_ne_zero h2 hirr m
  have h4 := cast_prod_sub_one (Nat.card F) 1 m 2 hq
  apply Nat.cast_injective (R := ℤ)
  rw [h3]
  simp only [lieOrderNumerator, Nat.add_sub_cancel]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, h4]
  push_cast
  ring

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
