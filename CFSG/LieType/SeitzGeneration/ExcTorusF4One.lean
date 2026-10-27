module

public import CFSG.LieType.SeitzGeneration.ExcTorusTors
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def f4OneWord : List (Fin Tag.F4.rank) :=
  []

@[expose] def f4OneMat : List (List ℤ) :=
  [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]

@[expose] def f4OneBasis : List (List ℤ) :=
  [[-1, -2, 1, 1], [2, 1, -1, 0], [-2, 1, -2, -1], [0, 1, 1, -1]]

@[expose] def f4OneBasisInv : List (List ℤ) :=
  [[3, 3, 1, 2], [-8, -7, -3, -5], [-2, -2, -1, -1], [-10, -9, -4, -7]]

theorem f4One_wordMat :
    wordMat Tag.F4 f4OneWord = toMat Tag.F4.rank f4OneMat :=
  wordMat_eq_toMat Tag.F4 _ (by decide +kernel)

theorem f4One_pow : (wordMat Tag.F4 f4OneWord) ^ 1 = 1 := by
  rw [f4One_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.F4.rank) (by decide +kernel)

theorem f4One_charpoly :
    (wordMat Tag.F4 f4OneWord).charpoly =
      ([1, 1, 1, 1].map fun d => cyclotomic d ℤ).prod := by
  rw [f4One_wordMat]
  exact charpoly_of_basis f4OneMat f4OneBasis f4OneBasisInv [1, 1, 1, 1]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem exists_elemAbelian_F4_one
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 1) :
    ∃ E : Subgroup (adjointGroup Tag.F4 K), IsElemAbelian p E ∧ Nat.card E = p ^ 4 := by
  have h := exists_elemAbelian_of_blocks_F4 K hp hp3
    (IsWeylMatrix.of_word Tag.F4 f4OneWord) [1, 1, 1, 1]
    f4One_charpoly f4One_pow he (by norm_num) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
