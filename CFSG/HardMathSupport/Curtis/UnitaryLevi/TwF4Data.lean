module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcF4Cent

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley


theorem twA_a_data :
    (1 - SM lbF = (1 - SM laF) * !![0, 0, 0, -2; 0, 0, 0, -3; 0, 0, 0, -6; 0, 0, 0, 0] + !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; -1, 0, 0, 1] *
      (1 + SM laF + SM laF * SM laF)) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((SM laF).mulVec ![2, 1, 0, 0]) i - ![2, 1, 0, 0] i) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((SM laF).mulVec ![0, 0, 0, 1]) i - ![0, 0, 0, 1] i) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel


theorem twA_b_data :
    (1 - SM laF = (1 - SM lbF) * !![0, 0, 0, 0; 0, 0, 0, 0; 3, 3, -3, 0; 1, 1, -1, 0] + !![0, 0, 0, 0; -1, 0, 0, 0; -1, -1, 0, 0; 0, 0, 0, 0] *
      (1 + SM lbF + SM lbF * SM lbF)) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((SM lbF).mulVec ![1, 0, 0, 0]) i - ![1, 0, 0, 0] i) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((SM lbF).mulVec ![0, 1, 0, 0]) i - ![0, 1, 0, 0] i) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel


@[expose] def twYs_ab : Fin 4 → List (Fin Tag.F4.rank) :=
  ![([0, 1] : List (Fin 4)), ([0, 1, 2, 3, 2, 1, 0, 2] : List (Fin 4)), ([1, 2, 1, 2, 3, 2] : List (Fin 4)), ([0, 1, 0, 2, 1, 0, 2, 3, 2, 1] : List (Fin 4))]


theorem twB_ab_data_tab : ∀ a b : Fin 3, ∃ i : Fin 4, ∃ d : Fin 4 → ℤ,
    (1 - SM lAB).mulVec d = (1 - SM (twYs_ab i)).mulVec
      (((a : ℕ) : ℤ) • ![0, 0, 1, 0] + ((b : ℕ) : ℤ) • ![0, 0, 0, 1]) := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact ⟨0, ![0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨0, ![0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨0, ![0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨1, ![1, 1, 2, 1], by decide +kernel⟩
  · exact ⟨2, ![0, 0, 1, 1], by decide +kernel⟩
  · exact ⟨3, ![-1, -1, -1, 0], by decide +kernel⟩
  · exact ⟨1, ![2, 2, 4, 2], by decide +kernel⟩
  · exact ⟨3, ![-1, -2, -2, -1], by decide +kernel⟩
  · exact ⟨2, ![0, 0, 2, 2], by decide +kernel⟩

theorem twB_ab_data :
    ((1 - SM lAB) * !![0, -1, 0, 0; -1, -1, 0, 0; -2, -2, 0, 0; 0, 0, 0, 0] + Matrix.vecMulVec ![0, 0, 1, 0] ![0, 0, 1, 0] +
      Matrix.vecMulVec ![0, 0, 0, 1] ![-2, -2, 0, 1] = 1) ∧
    ((1 - SM lAB).mulVec ![1, 1, 3, 1] = (3 : ℤ) • ![0, 0, 1, 0]) ∧
    ((1 - SM lAB).mulVec ![-1, -2, -3, 0] = (3 : ℤ) • ![0, 0, 0, 1]) ∧
    ((1 - SM lAB) * !![2, -1, 1, -1; 1, 1, 1, -2; 0, 0, 3, -3; 0, 0, 1, 0] = (3 : ℤ) • 1) ∧
    (∀ i : Fin 4, SM lAB * SM (twYs_ab i) = SM (twYs_ab i) * SM lAB) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((SM lAB).mulVec ![2, 1, 0, 0]) i - ![2, 1, 0, 0] i) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((SM lAB).mulVec ![2, 0, 0, 1]) i - ![2, 0, 0, 1] i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · decide +kernel
  · decide +kernel


@[expose] def twYs_ab2 : Fin 4 → List (Fin Tag.F4.rank) :=
  ![([0, 1] : List (Fin 4)), ([1, 2, 3, 2, 1, 2] : List (Fin 4)), ([0, 1, 2, 1, 0, 2, 3, 2] : List (Fin 4)), ([0, 1, 0, 2, 3, 2, 1, 0, 2, 1] : List (Fin 4))]


theorem twB_ab2_data_tab : ∀ a b : Fin 3, ∃ i : Fin 4, ∃ d : Fin 4 → ℤ,
    (1 - SM lAB2).mulVec d = (1 - SM (twYs_ab2 i)).mulVec
      (((a : ℕ) : ℤ) • ![0, 0, 1, 0] + ((b : ℕ) : ℤ) • ![0, 0, 0, 1]) := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact ⟨0, ![0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨0, ![0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨0, ![0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨1, ![0, 0, 1, 0], by decide +kernel⟩
  · exact ⟨2, ![1, 1, 2, 1], by decide +kernel⟩
  · exact ⟨3, ![0, -1, -1, 0], by decide +kernel⟩
  · exact ⟨1, ![0, 0, 2, 0], by decide +kernel⟩
  · exact ⟨3, ![-1, -2, -2, -1], by decide +kernel⟩
  · exact ⟨2, ![2, 2, 4, 2], by decide +kernel⟩

theorem twB_ab2_data :
    ((1 - SM lAB2) * !![1, 0, 0, 0; 0, 0, 0, 0; 1, 1, 0, 0; 0, 0, 0, 0] + Matrix.vecMulVec ![0, 0, 1, 0] ![-3, -3, 1, 0] +
      Matrix.vecMulVec ![0, 0, 0, 1] ![-1, -1, 0, 1] = 1) ∧
    ((1 - SM lAB2).mulVec ![0, -1, 0, -1] = (3 : ℤ) • ![0, 0, 1, 0]) ∧
    ((1 - SM lAB2).mulVec ![1, 2, 3, 3] = (3 : ℤ) • ![0, 0, 0, 1]) ∧
    ((1 - SM lAB2) * !![2, -1, 0, 1; 1, 1, -1, 2; 0, 0, 0, 3; 0, 0, -1, 3] = (3 : ℤ) • 1) ∧
    (∀ i : Fin 4, SM lAB2 * SM (twYs_ab2 i) = SM (twYs_ab2 i) * SM lAB2) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((SM lAB2).mulVec ![2, 1, 0, 0]) i - ![2, 1, 0, 0] i) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((SM lAB2).mulVec ![1, 0, 0, 1]) i - ![1, 0, 0, 1] i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · decide +kernel
  · decide +kernel

theorem twYs_ab_W :
    SM (lAB ++ lAB ++ lAB) = SM [] ∧ SM lAB ≠ SM [] ∧ ∀ i : Fin 4,
      SM (twYs_ab i ++ twYs_ab i ++ twYs_ab i) = SM [] ∧ SM (twYs_ab i) ≠ SM lAB ∧
      SM (twYs_ab i) ≠ SM [] ∧ SM (twYs_ab i) ≠ SM (lAB ++ lAB) ∧
      SM (lAB ++ twYs_ab i) = SM (twYs_ab i ++ lAB) := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> decide +kernel

theorem twYs_ab2_W :
    SM (lAB2 ++ lAB2 ++ lAB2) = SM [] ∧ SM lAB2 ≠ SM [] ∧ ∀ i : Fin 4,
      SM (twYs_ab2 i ++ twYs_ab2 i ++ twYs_ab2 i) = SM [] ∧ SM (twYs_ab2 i) ≠ SM lAB2 ∧
      SM (twYs_ab2 i) ≠ SM [] ∧ SM (twYs_ab2 i) ≠ SM (lAB2 ++ lAB2) ∧
      SM (lAB2 ++ twYs_ab2 i) = SM (twYs_ab2 i ++ lAB2) := by
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> decide +kernel

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
