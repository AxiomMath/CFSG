module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcF4W
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcIntSolve

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Curtis.UnitaryLevi (Smat laF lbF solve_int_fpf)

noncomputable abbrev ATw (l : List (Fin Tag.F4.rank)) : Matrix (Fin 4) (Fin 4) ℤ :=
  ((l.reverse.map (Smat Tag.F4)).prod).transpose

@[expose] def twLAB : List (Fin Tag.F4.rank) := laF ++ lbF

@[expose] def twLAB2 : List (Fin Tag.F4.rank) := laF ++ lbF ++ lbF

theorem twA_a_data :
    (1 - ATw lbF = (1 - ATw laF) * !![-1, -2, -3, -1; -1, -2, -3, -1; 0, 0, 0, 0; 0, 0, 0, 0] +
      !![0, 0, 3, 1; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, -1, 0] *
      (1 + ATw laF + ATw laF * ATw laF)) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((ATw laF).mulVec ![0, 0, 1, 0]) i - ![0, 0, 1, 0] i) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((ATw laF).mulVec ![0, 0, 0, 1]) i - ![0, 0, 0, 1] i) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem twA_b_data :
    (1 - ATw laF = (1 - ATw lbF) * !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, -1, 0, 0] +
      !![0, -1, -2, 0; 0, 1, 1, 0; 0, 0, 0, 0; 0, 0, 0, 0] *
      (1 + ATw lbF + ATw lbF * ATw lbF)) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((ATw lbF).mulVec ![1, 1, 0, 0]) i - ![1, 1, 0, 0] i) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((ATw lbF).mulVec ![0, 0, 1, 0]) i - ![0, 0, 1, 0] i) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

@[expose] def twYsAB : Fin 2 → List (Fin Tag.F4.rank) :=
  ![lbF, laF ++ lbF]

theorem twB_ab_data :
    ((1 - ATw twLAB) * !![0, 0, 0, 0; -1, 4, 0, 1; 1, -3, 0, -1; -4, 9, 1, 3] +
      Matrix.vecMulVec ![-1, -1, -1, 0] ![-1, 3, 0, 1] +
      Matrix.vecMulVec ![-1, 0, -1, -1] ![-1, 1, 0, 0] = 1) ∧
    ((1 - ATw twLAB).mulVec ![0, -3, 2, -6] = (3 : ℤ) • ![-1, -1, -1, 0]) ∧
    ((1 - ATw twLAB).mulVec ![-1, -1, 2, -7] = (3 : ℤ) • ![-1, 0, -1, -1]) ∧
    ((1 - ATw twLAB) * (2 + ATw twLAB) = (3 : ℤ) • 1) ∧
    (∀ i : Fin 2, ATw twLAB * ATw (twYsAB i) = ATw (twYsAB i) * ATw twLAB) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((ATw twLAB).mulVec ![1, 1, 0, 1]) i - ![1, 1, 0, 1] i) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((ATw twLAB).mulVec ![0, 0, 1, 0]) i - ![0, 0, 1, 0] i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · decide +kernel
  · decide +kernel

@[expose] def twYsAB2 : Fin 2 → List (Fin Tag.F4.rank) :=
  ![lbF, laF ++ lbF ++ lbF]

theorem twB_ab2_data :
    ((1 - ATw twLAB2) * !![0, 0, 0, 0; -4, 6, 3, 1; -8, 10, 6, 2; 9, -12, -7, -2] +
      Matrix.vecMulVec ![-1, -1, -1, -1] ![-4, 5, 3, 1] +
      Matrix.vecMulVec ![-1, 0, -1, -1] ![-1, 1, 0, 0] = 1) ∧
    ((1 - ATw twLAB2).mulVec ![0, -3, -5, 6] = (3 : ℤ) • ![-1, -1, -1, -1]) ∧
    ((1 - ATw twLAB2).mulVec ![-1, -1, -4, 4] = (3 : ℤ) • ![-1, 0, -1, -1]) ∧
    ((1 - ATw twLAB2) * (2 + ATw twLAB2) = (3 : ℤ) • 1) ∧
    (∀ i : Fin 2, ATw twLAB2 * ATw (twYsAB2 i) = ATw (twYsAB2 i) * ATw twLAB2) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((ATw twLAB2).mulVec ![1, 1, 0, -1]) i - ![1, 1, 0, -1] i) ∧
    (∀ i : Fin 4, (3 : ℤ) ∣ ((ATw twLAB2).mulVec ![0, 0, 1, 0]) i - ![0, 0, 1, 0] i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · decide +kernel
  · decide +kernel

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

end
