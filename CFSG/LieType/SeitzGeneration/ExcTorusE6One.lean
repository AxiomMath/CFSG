module

public import CFSG.LieType.SeitzGeneration.ExcTorusTors
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e6OneWord : List (Fin Tag.E6.rank) :=
  []

@[expose] def e6OneMat : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]]

@[expose] def e6OneBasis : List (List ℤ) :=
  [[-1, 1, 0, -2, 1, 0], [2, 1, -1, -2, -2, -1], [-2, 1, 2, 2, 2, 0], [0, -1, -2, -2, -1, 0],
   [-2, -2, 0, 1, 1, 1], [1, 1, -2, -1, 1, 0]]

@[expose] def e6OneBasisInv : List (List ℤ) :=
  [[1, 10, 0, -7, 10, 2], [-2, -22, -1, 14, -22, -4], [1, 7, 0, -5, 7, 1], [-1, -6, 0, 4, -6, -1],
   [2, 20, 1, -13, 20, 4], [-3, -38, -3, 23, -37, -7]]

theorem e6One_wordMat :
    wordMat Tag.E6 e6OneWord = toMat Tag.E6.rank e6OneMat :=
  wordMat_eq_toMat Tag.E6 _ (by decide +kernel)

theorem e6One_pow : (wordMat Tag.E6 e6OneWord) ^ 1 = 1 := by
  rw [e6One_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E6.rank) (by decide +kernel)

theorem e6One_charpoly :
    (wordMat Tag.E6 e6OneWord).charpoly =
      ([1, 1, 1, 1, 1, 1].map fun d => cyclotomic d ℤ).prod := by
  rw [e6One_wordMat]
  exact charpoly_of_basis e6OneMat e6OneBasis e6OneBasisInv [1, 1, 1, 1, 1, 1]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem exists_elemAbelian_E6_one
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 1) :
    ∃ E : Subgroup (adjointGroup Tag.E6 K), IsElemAbelian p E ∧ Nat.card E = p ^ 6 := by
  have h := exists_elemAbelian_of_blocks 3 (Or.inl ⟨rfl, rfl⟩) K hp hp3
    (IsWeylMatrix.of_word Tag.E6 e6OneWord) [1, 1, 1, 1, 1, 1]
    e6One_charpoly e6One_pow he (by norm_num) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
