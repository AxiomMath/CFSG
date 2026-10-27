module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcF4W
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcTorusAct

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

@[expose] abbrev RM (l : List (Fin Tag.F4.rank)) : Matrix (Fin 4) (Fin 4) ℤ :=
  (l.map (Rmat Tag.F4)).prod

@[expose] def lAB : List (Fin Tag.F4.rank) := laF ++ lbF

@[expose] def lAB2 : List (Fin Tag.F4.rank) := laF ++ lbF ++ lbF

theorem boundA_a_data :
    (1 - RM lbF = (1 - RM laF) * !![0, 0, 0, -4; 0, 0, 0, -6; 0, 0, 0, -6; 0, 0, 0, 0] + !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 1; 1, 0, -1, 1] *
      (1 + RM laF + RM laF * RM laF)) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((RM laF).mulVec ![2, 1, 0, 0]) i - ![2, 1, 0, 0] i) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((RM laF).mulVec ![0, 0, 0, 1]) i - ![0, 0, 0, 1] i) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel


theorem boundA_b_data :
    (1 - RM laF = (1 - RM lbF) * !![0, 0, 0, 0; 0, 0, 0, 0; -3, -3, 6, 0; -1, -1, 2, 0] + !![1, 1, 0, 0; 1, 2, 0, 0; 1, 1, 0, 0; 0, 0, 0, 0] *
      (1 + RM lbF + RM lbF * RM lbF)) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((RM lbF).mulVec ![1, 0, 0, 0]) i - ![1, 0, 0, 0] i) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((RM lbF).mulVec ![0, 1, 0, 0]) i - ![0, 1, 0, 0] i) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel


@[expose] def ys_ab : Fin 4 → List (Fin Tag.F4.rank) :=
  ![([0, 1] : List (Fin 4)), ([0, 1, 2, 3, 2, 1, 0, 2] : List (Fin 4)), ([1, 2, 1, 2, 3, 2] : List (Fin 4)), ([0, 1, 0, 2, 1, 0, 2, 3, 2, 1] : List (Fin 4))]


theorem boundB_ab_data_tab : ∀ a b : Fin 3, ∃ i : Fin 4, ∃ d : Fin 4 → ℤ,
    (1 - RM lAB).mulVec d = (1 - RM (ys_ab i)).mulVec
      (((a : ℕ) : ℤ) • ![0, 0, 1, 0] + ((b : ℕ) : ℤ) • ![0, 0, 0, 1]) := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact ⟨0, ![0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨0, ![0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨0, ![0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨1, ![2, 2, 2, 1], by decide +kernel⟩
  · exact ⟨2, ![0, 0, 1, 1], by decide +kernel⟩
  · exact ⟨3, ![-2, -2, -1, 0], by decide +kernel⟩
  · exact ⟨1, ![4, 4, 4, 2], by decide +kernel⟩
  · exact ⟨3, ![-2, -4, -2, -1], by decide +kernel⟩
  · exact ⟨2, ![0, 0, 2, 2], by decide +kernel⟩

theorem boundB_ab_data :
    ((1 - RM lAB) * !![0, -1, 0, 0; -1, -1, 0, 0; -1, -1, 0, 0; 0, 0, 0, 0] + Matrix.vecMulVec ![0, 0, 1, 0] ![0, 0, 1, 0] +
      Matrix.vecMulVec ![0, 0, 0, 1] ![-1, -1, 0, 1] = 1) ∧
    ((1 - RM lAB).mulVec ![2, 2, 3, 1] = (3 : ℤ) • ![0, 0, 1, 0]) ∧
    ((1 - RM lAB).mulVec ![-2, -4, -3, 0] = (3 : ℤ) • ![0, 0, 0, 1]) ∧
    ((1 - RM lAB) * !![2, -1, 2, -2; 1, 1, 2, -4; 0, 0, 3, -3; 0, 0, 1, 0] = (3 : ℤ) • 1) ∧
    (∀ i : Fin 4, RM lAB * RM (ys_ab i) = RM (ys_ab i) * RM lAB) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((RM lAB).mulVec ![2, 1, 0, 0]) i - ![2, 1, 0, 0] i) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((RM lAB).mulVec ![1, 0, 0, 1]) i - ![1, 0, 0, 1] i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · decide +kernel
  · decide +kernel


@[expose] def ys_ab2 : Fin 4 → List (Fin Tag.F4.rank) :=
  ![([0, 1] : List (Fin 4)), ([1, 2, 3, 2, 1, 2] : List (Fin 4)), ([0, 1, 2, 1, 0, 2, 3, 2] : List (Fin 4)), ([0, 1, 0, 2, 3, 2, 1, 0, 2, 1] : List (Fin 4))]


theorem boundB_ab2_data_tab : ∀ a b : Fin 3, ∃ i : Fin 4, ∃ d : Fin 4 → ℤ,
    (1 - RM lAB2).mulVec d = (1 - RM (ys_ab2 i)).mulVec
      (((a : ℕ) : ℤ) • ![0, 0, 1, 0] + ((b : ℕ) : ℤ) • ![0, 0, 0, 1]) := by
  intro a b
  fin_cases a <;> fin_cases b
  · exact ⟨0, ![0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨0, ![0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨0, ![0, 0, 0, 0], by decide +kernel⟩
  · exact ⟨1, ![0, 0, 1, 0], by decide +kernel⟩
  · exact ⟨2, ![2, 2, 2, 1], by decide +kernel⟩
  · exact ⟨3, ![0, -2, -1, 0], by decide +kernel⟩
  · exact ⟨1, ![0, 0, 2, 0], by decide +kernel⟩
  · exact ⟨3, ![-2, -4, -2, -1], by decide +kernel⟩
  · exact ⟨2, ![4, 4, 4, 2], by decide +kernel⟩

theorem boundB_ab2_data :
    ((1 - RM lAB2) * !![0, -1, 0, 0; 1, 1, 0, 0; -1, -1, 0, 0; 0, 0, 0, 0] + Matrix.vecMulVec ![0, 0, 1, 0] ![3, 3, 1, 0] +
      Matrix.vecMulVec ![0, 0, 0, 1] ![1, 1, 0, 1] = 1) ∧
    ((1 - RM lAB2).mulVec ![0, -2, 0, -1] = (3 : ℤ) • ![0, 0, 1, 0]) ∧
    ((1 - RM lAB2).mulVec ![2, 4, 3, 3] = (3 : ℤ) • ![0, 0, 0, 1]) ∧
    ((1 - RM lAB2) * !![2, -1, 0, 2; 1, 1, -2, 4; 0, 0, 0, 3; 0, 0, -1, 3] = (3 : ℤ) • 1) ∧
    (∀ i : Fin 4, RM lAB2 * RM (ys_ab2 i) = RM (ys_ab2 i) * RM lAB2) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((RM lAB2).mulVec ![2, 1, 0, 0]) i - ![2, 1, 0, 0] i) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((RM lAB2).mulVec ![2, 0, 0, 1]) i - ![2, 0, 0, 1] i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · decide +kernel
  · decide +kernel

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
