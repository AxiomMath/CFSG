module

public import CFSG.LieType.SeitzGeneration.ExcTorusTors
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def f4TwoWord : List (Fin Tag.F4.rank) :=
  [0, 1, 0, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3, 2, 1, 0, 2, 1, 2, 3]

@[expose] def f4TwoMat : List (List ℤ) :=
  [[-1, 0, 0, 0], [0, -1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]]

@[expose] def f4TwoBasis : List (List ℤ) :=
  [[-1, -2, 1, 1], [2, 1, -1, 0], [-2, 1, -2, -1], [0, 1, 1, -1]]

@[expose] def f4TwoBasisInv : List (List ℤ) :=
  [[3, 3, 1, 2], [-8, -7, -3, -5], [-2, -2, -1, -1], [-10, -9, -4, -7]]

theorem f4Two_wordMat :
    wordMat Tag.F4 f4TwoWord = toMat Tag.F4.rank f4TwoMat :=
  wordMat_eq_toMat Tag.F4 _ (by decide +kernel)

theorem f4Two_pow : (wordMat Tag.F4 f4TwoWord) ^ 2 = 1 := by
  rw [f4Two_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.F4.rank) (by decide +kernel)

theorem f4Two_charpoly :
    (wordMat Tag.F4 f4TwoWord).charpoly =
      ([2, 2, 2, 2].map fun d => cyclotomic d ℤ).prod := by
  rw [f4Two_wordMat]
  exact charpoly_of_basis f4TwoMat f4TwoBasis f4TwoBasisInv [2, 2, 2, 2]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem exists_elemAbelian_F4_two
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) :
    ∃ E : Subgroup (adjointGroup Tag.F4 K), IsElemAbelian p E ∧ Nat.card E = p ^ 4 := by
  have h := exists_elemAbelian_of_blocks_F4 K hp hp3
    (IsWeylMatrix.of_word Tag.F4 f4TwoWord) [2, 2, 2, 2]
    f4Two_charpoly f4Two_pow he (by norm_num) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
