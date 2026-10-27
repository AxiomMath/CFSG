module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNE6Two
public import CFSG.RankThree.E6.LargePrimeStabilizers

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Curtis.UnitaryLevi

@[expose] def cwE6 : Fin 45 → List (Fin Tag.E6.rank) :=
  ![([] : List (Fin 6)),
    ([0] : List (Fin 6)),
    ([5] : List (Fin 6)),
    ([2, 0] : List (Fin 6)),
    ([5, 0] : List (Fin 6)),
    ([4, 5] : List (Fin 6)),
    ([3, 2, 0] : List (Fin 6)),
    ([5, 2, 0] : List (Fin 6)),
    ([4, 5, 0] : List (Fin 6)),
    ([3, 4, 5] : List (Fin 6)),
    ([1, 3, 2, 0] : List (Fin 6)),
    ([5, 3, 2, 0] : List (Fin 6)),
    ([4, 5, 2, 0] : List (Fin 6)),
    ([3, 4, 5, 0] : List (Fin 6)),
    ([1, 3, 4, 5] : List (Fin 6)),
    ([5, 1, 3, 2, 0] : List (Fin 6)),
    ([4, 5, 3, 2, 0] : List (Fin 6)),
    ([3, 4, 5, 2, 0] : List (Fin 6)),
    ([1, 3, 4, 5, 0] : List (Fin 6)),
    ([2, 3, 4, 5, 0] : List (Fin 6)),
    ([4, 5, 1, 3, 2, 0] : List (Fin 6)),
    ([3, 4, 5, 3, 2, 0] : List (Fin 6)),
    ([1, 3, 4, 5, 2, 0] : List (Fin 6)),
    ([2, 3, 4, 5, 2, 0] : List (Fin 6)),
    ([2, 1, 3, 4, 5, 0] : List (Fin 6)),
    ([3, 4, 5, 1, 3, 2, 0] : List (Fin 6)),
    ([1, 3, 4, 5, 3, 2, 0] : List (Fin 6)),
    ([2, 3, 4, 5, 3, 2, 0] : List (Fin 6)),
    ([2, 1, 3, 4, 5, 2, 0] : List (Fin 6)),
    ([0, 2, 3, 4, 5, 2, 0] : List (Fin 6)),
    ([1, 3, 4, 5, 1, 3, 2, 0] : List (Fin 6)),
    ([2, 3, 4, 5, 1, 3, 2, 0] : List (Fin 6)),
    ([2, 1, 3, 4, 5, 3, 2, 0] : List (Fin 6)),
    ([0, 2, 3, 4, 5, 3, 2, 0] : List (Fin 6)),
    ([0, 2, 1, 3, 4, 5, 2, 0] : List (Fin 6)),
    ([2, 1, 3, 4, 5, 1, 3, 2, 0] : List (Fin 6)),
    ([0, 2, 3, 4, 5, 1, 3, 2, 0] : List (Fin 6)),
    ([0, 2, 1, 3, 4, 5, 3, 2, 0] : List (Fin 6)),
    ([3, 2, 1, 3, 4, 5, 3, 2, 0] : List (Fin 6)),
    ([0, 2, 1, 3, 4, 5, 1, 3, 2, 0] : List (Fin 6)),
    ([3, 2, 1, 3, 4, 5, 1, 3, 2, 0] : List (Fin 6)),
    ([3, 0, 2, 1, 3, 4, 5, 3, 2, 0] : List (Fin 6)),
    ([3, 0, 2, 1, 3, 4, 5, 1, 3, 2, 0] : List (Fin 6)),
    ([4, 3, 2, 1, 3, 4, 5, 1, 3, 2, 0] : List (Fin 6)),
    ([2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 2, 0] : List (Fin 6))]

@[expose] def LcE6 (i : Fin 45) : List (Fin Tag.E6.rank) :=
  cwE6 i ++ e6TwoWord ++ (cwE6 i).reverse

@[expose] def MatTabC : Fin 45 → Matrix (Fin 6) (Fin 6) ℤ :=
  ![!![1, 0, 0, 0, 0, 0; 1, -1, 0, 0, 0, 1; 2, 0, -1, 0, 0, 1; 2, 0, 0, -1, 0, 2; 1, 0, 0, 0, -1, 2; 0, 0, 0, 0, 0, 1],
    !![-1, 0, 0, 0, 0, 1; -1, -1, 1, 0, 0, 1; -2, 0, 1, 0, 0, 1; -2, 0, 2, -1, 0, 2; -1, 0, 1, 0, -1, 2; 0, 0, 0, 0, 0, 1],
    !![1, 0, 0, 0, 0, 0; 1, -1, 0, 0, 1, -1; 2, 0, -1, 0, 1, -1; 2, 0, 0, -1, 2, -2; 1, 0, 0, 0, 1, -2; 1, 0, 0, 0, 0, -1],
    !![-1, 0, 0, 0, 0, 1; 0, -1, -1, 1, 0, 1; 0, 0, -1, 0, 0, 2; 0, 0, -2, 1, 0, 2; 0, 0, -1, 1, -1, 2; 0, 0, 0, 0, 0, 1],
    !![-1, 0, 0, 0, 1, -1; -1, -1, 1, 0, 1, -1; -2, 0, 1, 0, 1, -1; -2, 0, 2, -1, 2, -2; -1, 0, 1, 0, 1, -2; -1, 0, 1, 0, 0, -1],
    !![1, 0, 0, 0, 0, 0; 1, -1, 0, 1, -1, 0; 2, 0, -1, 1, -1, 0; 2, 0, 0, 1, -2, 0; 2, 0, 0, 0, -1, 0; 1, 0, 0, 0, 0, -1],
    !![-1, 0, 0, 0, 0, 1; 0, 0, 0, -1, 1, 1; 0, 0, -1, 0, 0, 2; 0, 0, 0, -1, 0, 3; 0, 1, 0, -1, 0, 2; 0, 0, 0, 0, 0, 1],
    !![-1, 0, 0, 0, 1, -1; 0, -1, -1, 1, 1, -1; 0, 0, -1, 0, 2, -2; 0, 0, -2, 1, 2, -2; 0, 0, -1, 1, 1, -2; 0, 0, -1, 1, 0, -1],
    !![-1, 0, 0, 1, -1, 0; -1, -1, 1, 1, -1, 0; -2, 0, 1, 1, -1, 0; -2, 0, 2, 1, -2, 0; -2, 0, 2, 0, -1, 0; -1, 0, 1, 0, 0, -1],
    !![1, 0, 0, 0, 0, 0; 1, 0, 1, -1, 0, 0; 2, 1, 0, -1, 0, 0; 3, 0, 0, -1, 0, 0; 2, 0, 0, 0, -1, 0; 1, 0, 0, 0, 0, -1],
    !![-1, 0, 0, 0, 0, 1; 0, 0, 0, 0, -1, 2; 0, 0, -1, 0, 0, 2; 0, 0, 0, -1, 0, 3; 0, -1, 0, 0, 0, 2; 0, 0, 0, 0, 0, 1],
    !![-1, 0, 0, 0, 1, -1; 0, 0, 0, -1, 2, -1; 0, 0, -1, 0, 2, -2; 0, 0, 0, -1, 3, -3; 0, 1, 0, -1, 2, -2; 0, 1, 0, -1, 1, -1],
    !![-1, 0, 0, 1, -1, 0; 0, -1, -1, 2, -1, 0; 0, 0, -1, 2, -2, 0; 0, 0, -2, 3, -2, 0; 0, 0, -2, 2, -1, 0; 0, 0, -1, 1, 0, -1],
    !![-1, 1, 1, -1, 0, 0; -1, 0, 2, -1, 0, 0; -2, 1, 2, -1, 0, 0; -3, 0, 3, -1, 0, 0; -2, 0, 2, 0, -1, 0; -1, 0, 1, 0, 0, -1],
    !![1, 0, 0, 0, 0, 0; 2, 0, -1, 0, 0, 0; 2, -1, 0, 0, 0, 0; 3, 0, 0, -1, 0, 0; 2, 0, 0, 0, -1, 0; 1, 0, 0, 0, 0, -1],
    !![-1, 0, 0, 0, 1, -1; 0, 0, 0, 0, 1, -2; 0, 0, -1, 0, 2, -2; 0, 0, 0, -1, 3, -3; 0, -1, 0, 0, 2, -2; 0, -1, 0, 0, 1, -1],
    !![-1, 0, 0, 1, -1, 0; 0, 0, 0, 1, -2, 1; 0, 0, -1, 2, -2, 0; 0, 0, 0, 2, -3, 0; 0, 0, 0, 1, -2, 0; 0, 1, 0, 0, -1, 0],
    !![-1, 1, 1, -1, 0, 0; 0, 1, 1, -2, 1, 0; 0, 2, 1, -2, 0, 0; 0, 2, 1, -3, 1, 0; 0, 2, 0, -2, 1, 0; 0, 1, 0, -1, 1, -1],
    !![-1, -1, 1, 0, 0, 0; -2, 0, 1, 0, 0, 0; -2, -1, 2, 0, 0, 0; -3, 0, 3, -1, 0, 0; -2, 0, 2, 0, -1, 0; -1, 0, 1, 0, 0, -1],
    !![0, 1, -1, 0, 0, 0; 1, 0, -2, 1, 0, 0; 0, 0, -2, 1, 0, 0; 0, 0, -3, 2, 0, 0; 0, 0, -2, 2, -1, 0; 0, 0, -1, 1, 0, -1],
    !![-1, 0, 0, 1, -1, 0; 0, 0, 0, 1, -1, -1; 0, 0, -1, 2, -2, 0; 0, 0, 0, 2, -3, 0; 0, 0, 0, 1, -2, 0; 0, -1, 0, 1, -1, 0],
    !![-1, 1, 1, -1, 0, 0; 0, 1, 1, -1, -1, 1; 0, 2, 1, -2, 0, 0; 0, 2, 1, -2, -1, 1; 0, 1, 1, -1, -1, 0; 0, 1, 0, 0, -1, 0],
    !![-1, -1, 1, 0, 0, 0; 0, -1, 0, 0, 0, 0; 0, -2, 1, 0, 0, 0; 0, -2, 1, -1, 1, 0; 0, -2, 0, 0, 1, 0; 0, -1, 0, 0, 1, -1],
    !![0, 1, -1, 0, 0, 0; 1, 1, -1, -1, 1, 0; 0, 1, -1, -1, 1, 0; 1, 2, -1, -2, 1, 0; 0, 2, 0, -2, 1, 0; 0, 1, 0, -1, 1, -1],
    !![0, -1, -1, 1, 0, 0; -1, 0, -1, 1, 0, 0; 0, 0, -2, 1, 0, 0; 0, 0, -3, 2, 0, 0; 0, 0, -2, 2, -1, 0; 0, 0, -1, 1, 0, -1],
    !![-1, 1, 1, -1, 0, 0; 0, 1, 1, -1, 0, -1; 0, 2, 1, -2, 0, 0; 0, 2, 1, -2, 0, -1; 0, 1, 1, -1, -1, 0; 0, 0, 1, -1, 0, 0],
    !![-1, -1, 1, 0, 0, 0; 0, -1, 0, 0, 0, 0; 0, -2, 1, 0, 0, 0; 0, -2, 1, 0, -1, 1; 0, -1, 1, 0, -1, 0; 0, -1, 0, 1, -1, 0],
    !![0, 1, -1, 0, 0, 0; 1, 1, -1, 0, -1, 1; 0, 1, -1, 0, -1, 1; 1, 2, -1, -1, -1, 1; 1, 1, -1, 0, -1, 0; 0, 1, 0, 0, -1, 0],
    !![0, -1, -1, 1, 0, 0; 0, -1, 0, 0, 0, 0; 0, -1, -1, 0, 1, 0; 1, -2, -1, 0, 1, 0; 0, -2, 0, 0, 1, 0; 0, -1, 0, 0, 1, -1],
    !![0, 0, 0, -1, 1, 0; -1, 1, 0, -1, 1, 0; 0, 1, -1, -1, 1, 0; -1, 2, 0, -2, 1, 0; 0, 2, 0, -2, 1, 0; 0, 1, 0, -1, 1, -1],
    !![-1, -1, 1, 0, 0, 0; 0, -1, 0, 0, 0, 0; 0, -2, 1, 0, 0, 0; 0, -2, 1, 0, 0, -1; 0, -1, 1, 0, -1, 0; 0, 0, 1, -1, 0, 0],
    !![0, 1, -1, 0, 0, 0; 1, 1, -1, 0, 0, -1; 0, 1, -1, 0, 0, -1; 1, 2, -1, -1, 0, -1; 1, 1, -1, 0, -1, 0; 1, 0, -1, 0, 0, 0],
    !![0, -1, -1, 1, 0, 0; 0, -1, 0, 0, 0, 0; 0, -1, -1, 1, -1, 1; 1, -2, -1, 1, -1, 1; 1, -1, -1, 1, -1, 0; 0, -1, 0, 1, -1, 0],
    !![0, 0, 0, 0, -1, 1; -1, 1, 0, 0, -1, 1; 0, 1, -1, 0, -1, 1; -1, 2, 0, -1, -1, 1; -1, 1, 0, 0, -1, 0; 0, 1, 0, 0, -1, 0],
    !![0, 0, 0, -1, 1, 0; 0, -1, 0, 0, 0, 0; 0, -1, -1, 0, 1, 0; -1, -2, 0, 0, 1, 0; 0, -2, 0, 0, 1, 0; 0, -1, 0, 0, 1, -1],
    !![0, -1, -1, 1, 0, 0; 0, -1, 0, 0, 0, 0; 0, -1, -1, 1, 0, -1; 1, -2, -1, 1, 0, -1; 1, -1, -1, 1, -1, 0; 1, 0, -1, 0, 0, 0],
    !![0, 0, 0, 0, 0, -1; -1, 1, 0, 0, 0, -1; 0, 1, -1, 0, 0, -1; -1, 2, 0, -1, 0, -1; -1, 1, 0, 0, -1, 0; -1, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, -1, 1; 0, -1, 0, 0, 0, 0; 0, -1, -1, 1, -1, 1; -1, -2, 0, 1, -1, 1; -1, -1, 0, 1, -1, 0; 0, -1, 0, 1, -1, 0],
    !![0, 0, 0, -1, 1, 0; 0, -1, 0, 0, 0, 0; 0, 0, 0, -1, 0, 1; 0, 0, 0, -1, 0, 0; 1, 0, 0, -1, 0, 0; 0, 0, 1, -1, 0, 0],
    !![0, 0, 0, 0, 0, -1; 0, -1, 0, 0, 0, 0; 0, -1, -1, 1, 0, -1; -1, -2, 0, 1, 0, -1; -1, -1, 0, 1, -1, 0; -1, 0, 0, 0, 0, 0],
    !![0, 0, 0, -1, 1, 0; 0, -1, 0, 0, 0, 0; 0, 0, 0, -1, 1, -1; 0, 0, 0, -1, 0, 0; 1, 0, 0, -1, 0, 0; 1, 0, -1, 0, 0, 0],
    !![0, 0, 0, 0, -1, 1; 0, -1, 0, 0, 0, 0; 0, 0, 0, -1, 0, 1; 0, 0, 0, -1, 0, 0; -1, 0, 1, -1, 0, 0; 0, 0, 1, -1, 0, 0],
    !![0, 0, 0, 0, 0, -1; 0, -1, 0, 0, 0, 0; 0, 0, 0, -1, 1, -1; 0, 0, 0, -1, 0, 0; -1, 0, 1, -1, 0, 0; -1, 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, -1, 1; 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0; 0, 0, 0, -1, 0, 0; 0, 0, -1, 0, 0, 0; 1, 0, -1, 0, 0, 0],
    !![0, 0, 0, 0, 0, -1; 0, -1, 0, 0, 0, 0; 0, 0, 0, 0, -1, 0; 0, 0, 0, -1, 0, 0; 0, 0, -1, 0, 0, 0; -1, 0, 0, 0, 0, 0]]

@[expose] def actTabC : Fin 6 → Fin 45 → Fin 45 :=
  ![![1, 0, 4, 3, 2, 8, 6, 7, 5, 13, 10, 11, 12, 9, 18, 15, 16, 17, 14, 24, 20, 21, 22, 29, 19, 25, 26, 33, 34, 23, 30, 36, 37, 27, 28, 39, 31, 32, 41, 35, 42, 38, 40, 44, 43],
    ![0, 1, 2, 3, 4, 5, 10, 7, 8, 14, 6, 15, 12, 18, 9, 11, 20, 22, 13, 24, 16, 26, 17, 28, 19, 30, 21, 32, 23, 34, 25, 35, 27, 37, 29, 31, 39, 33, 38, 36, 40, 41, 42, 43, 44],
    ![0, 3, 2, 1, 7, 5, 6, 4, 12, 14, 10, 11, 8, 19, 9, 15, 16, 23, 24, 13, 20, 27, 28, 17, 18, 31, 32, 21, 22, 29, 35, 25, 26, 33, 34, 30, 36, 37, 40, 39, 38, 43, 44, 41, 42],
    ![0, 1, 2, 6, 4, 9, 3, 11, 13, 5, 10, 7, 17, 8, 14, 15, 21, 12, 18, 23, 25, 16, 22, 19, 29, 20, 30, 27, 34, 24, 26, 31, 38, 33, 28, 40, 36, 41, 32, 42, 35, 37, 39, 43, 44],
    ![0, 1, 5, 3, 8, 2, 10, 12, 4, 9, 6, 16, 7, 13, 14, 20, 11, 21, 18, 19, 15, 17, 26, 27, 24, 25, 22, 23, 32, 33, 30, 31, 28, 29, 37, 35, 36, 34, 41, 39, 43, 38, 44, 40, 42],
    ![2, 4, 0, 7, 1, 5, 11, 3, 8, 9, 15, 6, 12, 13, 14, 10, 20, 17, 18, 19, 16, 25, 22, 23, 24, 21, 30, 31, 28, 29, 26, 27, 35, 36, 34, 32, 33, 39, 40, 37, 38, 42, 41, 44, 43]]

noncomputable abbrev SMC (l : List (Fin Tag.E6.rank)) : Matrix (Fin 6) (Fin 6) ℤ :=
  (l.map (Smat Tag.E6)).prod

noncomputable abbrev SmC (j : Fin 6) : Matrix (Fin 6) (Fin 6) ℤ := Smat Tag.E6 j

theorem SMC_Lc : ∀ i, SMC (LcE6 i) = MatTabC i := by decide +kernel

theorem act_okC : ∀ j i, SmC j * MatTabC i * SmC j = MatTabC (actTabC j i) := by
  decide +kernel

theorem MatTabC_inj : ∀ i j, MatTabC i = MatTabC j → i = j := by decide +kernel

section Weyl


theorem wordW_eq_iffC (l l' : List (Fin Tag.E6.rank)) :
    wordW Tag.E6 l = wordW Tag.E6 l' ↔ SMC l = SMC l' :=
  ⟨matrix_eq_of_wordW_eq Tag.E6 l l', wordW_eq_of_matrix Tag.E6 l l'⟩

theorem wordW_reverseC (l : List (Fin Tag.E6.rank)) :
    wordW Tag.E6 l.reverse = (wordW Tag.E6 l)⁻¹ :=
  (coxeterSystem Tag.E6).wordProd_reverse l

theorem wordW_Lc (i : Fin 45) :
    wordW Tag.E6 (LcE6 i) = wordW Tag.E6 (cwE6 i) * ww6 * (wordW Tag.E6 (cwE6 i))⁻¹ := by
  rw [LcE6, wordW_append, wordW_append, wordW_reverseC]
  rfl

theorem conj_simple_Lc (j : Fin Tag.E6.rank) (i : Fin 45) :
    simple Tag.E6 j * wordW Tag.E6 (LcE6 i) * (simple Tag.E6 j)⁻¹ =
      wordW Tag.E6 (LcE6 (actTabC j i)) := by
  have hinv : (simple Tag.E6 j)⁻¹ = simple Tag.E6 j := (coxeterSystem Tag.E6).inv_simple j
  have hs : simple Tag.E6 j = wordW Tag.E6 [j] := by simp [wordW]
  rw [hinv, hs, ← wordW_append, ← wordW_append, wordW_eq_iffC]
  have h1 : SMC ([j] ++ LcE6 i ++ [j]) = SmC j * SMC (LcE6 i) * SmC j := by
    simp [SMC, SmC, List.prod_append]
    exact (Matrix.mul_assoc _ _ _).symm
  rw [h1, SMC_Lc, SMC_Lc]
  exact act_okC j i

theorem conj_reach (l : List (Fin Tag.E6.rank)) :
    ∃ i : Fin 45, (coxeterSystem Tag.E6).wordProd l * ww6 *
      ((coxeterSystem Tag.E6).wordProd l)⁻¹ = wordW Tag.E6 (LcE6 i) := by
  induction l with
  | nil =>
    refine ⟨0, ?_⟩
    have hc : cwE6 0 = [] := rfl
    rw [wordW_Lc, hc]
    simp [wordW]
  | cons j l ih =>
    obtain ⟨i, hi⟩ := ih
    refine ⟨actTabC j i, ?_⟩
    rw [← conj_simple_Lc, ← hi, (coxeterSystem Tag.E6).wordProd_cons, mul_inv_rev,
      (coxeterSystem Tag.E6).inv_simple]
    show _ = (coxeterSystem Tag.E6).simple j * _ * (coxeterSystem Tag.E6).simple j
    simp only [mul_assoc]

theorem card_conjClass_mul_card_centralizer {N : Type} [Group N] (s : N) :
    Nat.card {y : N | ∃ x : N, y = x * s * x⁻¹} * Nat.card (Subgroup.centralizer ({s} : Set N)) =
      Nat.card N := by
  have e1 : {y : N | ∃ x : N, y = x * s * x⁻¹} = MulAction.orbit (ConjAct N) s := by
    ext y
    simp only [Set.mem_ofPred_eq, MulAction.mem_orbit_iff, ConjAct.smul_def]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨ConjAct.toConjAct x, by simp⟩
    · rintro ⟨c, rfl⟩
      exact ⟨ConjAct.ofConjAct c, rfl⟩
  have hmem : ∀ x : N, x ∈ Subgroup.centralizer ({s} : Set N) ↔
      ConjAct.toConjAct x ∈ MulAction.stabilizer (ConjAct N) s := by
    intro x
    rw [Subgroup.centralizer_eq_comap_stabilizer]
    rfl
  have e2 : Nat.card (MulAction.stabilizer (ConjAct N) s) =
      Nat.card (Subgroup.centralizer ({s} : Set N)) :=
    Nat.card_congr
      { toFun := fun c => ⟨ConjAct.ofConjAct c.1, (hmem _).2 c.2⟩
        invFun := fun x => ⟨ConjAct.toConjAct x.1, (hmem _).1 x.2⟩
        left_inv := fun c => rfl
        right_inv := fun x => rfl }
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct N) s)
  rw [Nat.card_prod, e2, Nat.card_congr (ConjAct.ofConjAct : ConjAct N ≃* N).toEquiv] at h
  rw [e1]
  exact h

theorem conjClass_eq :
    {y : WeylGroup Tag.E6 | ∃ x : WeylGroup Tag.E6, y = x * ww6 * x⁻¹} =
      Set.range (fun i : Fin 45 => wordW Tag.E6 (LcE6 i)) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨l, rfl⟩ := (coxeterSystem Tag.E6).wordProd_surjective x
    obtain ⟨i, hi⟩ := conj_reach l
    exact ⟨i, hi.symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨wordW Tag.E6 (cwE6 i), wordW_Lc i⟩

theorem Lc_inj : Function.Injective (fun i : Fin 45 => wordW Tag.E6 (LcE6 i)) := by
  intro i j h
  have := (wordW_eq_iffC _ _).1 h
  rw [SMC_Lc, SMC_Lc] at this
  exact MatTabC_inj _ _ this

theorem card_conjClass_e6Two :
    Nat.card {y : WeylGroup Tag.E6 | ∃ x : WeylGroup Tag.E6, y = x * ww6 * x⁻¹} = 45 := by
  rw [conjClass_eq, ← Nat.card_congr (Equiv.ofInjective _ Lc_inj)]
  simp

theorem card_centralizer_e6Two :
    Nat.card (Subgroup.centralizer
      ({(coxeterSystem Tag.E6).wordProd e6TwoWord} : Set (WeylGroup Tag.E6))) = 1152 := by
  have h := card_conjClass_mul_card_centralizer ww6
  rw [card_conjClass_e6Two, CFSG.RankThree.E6.card_weylGroup_E6] at h
  rw [← ww6_eq]
  omega

theorem factorization_1152 : (1152 : ℕ).factorization 3 = 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.factorization_def _ Nat.prime_three, show (1152 : ℕ) = 3 ^ 2 * 128 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem exists_conj_mem_sylow_threeC {G : Type*} [Group G] [Finite G] (Q : Sylow 3 G) (x : G)
    (hx : x ^ 3 = 1) : ∃ w : G, w * x * w⁻¹ ∈ (Q : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.zpowers x) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    show (x ^ n) ^ 3 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  obtain ⟨P, hP'⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  have hxP : x ∈ (P : Subgroup G) := hP' (Subgroup.mem_zpowers x)
  rw [← hg] at hxP
  refine ⟨g⁻¹, ?_⟩
  rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at hxP
  obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.1 hxP
  have hx' : g⁻¹ * x * g = s := by
    rw [← hsx]
    simp [MulAut.conj_apply, mul_assoc]
  rw [inv_inv, hx']
  exact hs

theorem exists_conj_centralizer_mem
    {Q : Subgroup (WeylGroup Tag.E6)}
    (hQ : Q ≤ Subgroup.centralizer
      ({(coxeterSystem Tag.E6).wordProd e6TwoWord} : Set (WeylGroup Tag.E6)))
    (hQc : Nat.card Q = 9) {x : WeylGroup Tag.E6}
    (hx : x ∈ Subgroup.centralizer
      ({(coxeterSystem Tag.E6).wordProd e6TwoWord} : Set (WeylGroup Tag.E6)))
    (hx3 : x ^ 3 = 1) :
    ∃ g ∈ Subgroup.centralizer
      ({(coxeterSystem Tag.E6).wordProd e6TwoWord} : Set (WeylGroup Tag.E6)),
      g * x * g⁻¹ ∈ Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCc := card_centralizer_e6Two
  set C := Subgroup.centralizer
      ({(coxeterSystem Tag.E6).wordProd e6TwoWord} : Set (WeylGroup Tag.E6)) with hC
  have hfin : Finite C := Nat.finite_of_card_ne_zero (by rw [hCc]; norm_num)
  have hQ' : Nat.card (Q.subgroupOf C) = 9 := by
    rw [← hQc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv
  let S : Sylow 3 C := Sylow.ofCard (Q.subgroupOf C)
    (by rw [hQ', hCc, factorization_1152]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow_threeC S ⟨x, hx⟩ (Subtype.ext (by simpa using hx3))
  have hS : (S : Subgroup C) = Q.subgroupOf C := rfl
  rw [hS, Subgroup.mem_subgroupOf] at hg
  exact ⟨g.1, g.2, hg⟩

theorem QE_card : Nat.card Q6 = 9 := Q6_card

theorem QE_le_centralizer :
    Q6 ≤ Subgroup.centralizer
      ({(coxeterSystem Tag.E6).wordProd e6TwoWord} : Set (WeylGroup Tag.E6)) :=
  Q6_le_centralizer

theorem exists_conj_centralizer_mem_Q6 {x : WeylGroup Tag.E6}
    (hx : x ∈ Subgroup.centralizer
      ({(coxeterSystem Tag.E6).wordProd e6TwoWord} : Set (WeylGroup Tag.E6)))
    (hx3 : x ^ 3 = 1) :
    ∃ g ∈ Subgroup.centralizer
      ({(coxeterSystem Tag.E6).wordProd e6TwoWord} : Set (WeylGroup Tag.E6)),
      g * x * g⁻¹ ∈ Q6 :=
  exists_conj_centralizer_mem QE_le_centralizer QE_card hx hx3

end Weyl

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

end
