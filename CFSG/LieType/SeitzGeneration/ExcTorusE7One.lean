module

public import CFSG.LieType.SeitzGeneration.ExcTorusTors
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e7OneWord : List (Fin Tag.E7.rank) :=
  []

@[expose] def e7OneMat : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def e7OneBasis : List (List ℤ) :=
  [[-1, 1, 1, 1, 1, 1, 2], [2, 1, 2, -1, 2, 0, 2], [-2, -1, -2, 1, -1, 1, 0],
   [0, -2, 1, -2, 0, -2, -1], [-2, 1, 0, 2, -1, 1, -1], [1, -2, -1, -1, -1, -2, -1],
   [1, 1, 2, 1, 1, 0, 2]]

@[expose] def e7OneBasisInv : List (List ℤ) :=
  [[-1, -1, 0, 0, -1, -1, 1], [2, 10, 2, -1, 8, 7, -5], [0, 9, 3, 0, 7, 5, -3],
   [-2, -21, -6, 1, -16, -13, 9], [-3, -40, -12, 2, -31, -25, 16], [-1, 7, 3, 0, 5, 3, -2],
   [2, 17, 5, -1, 13, 11, -7]]

theorem e7One_wordMat :
    wordMat Tag.E7 e7OneWord = toMat Tag.E7.rank e7OneMat :=
  wordMat_eq_toMat Tag.E7 _ (by decide +kernel)

theorem e7One_pow : (wordMat Tag.E7 e7OneWord) ^ 1 = 1 := by
  rw [e7One_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7One_charpoly :
    (wordMat Tag.E7 e7OneWord).charpoly =
      ([1, 1, 1, 1, 1, 1, 1].map fun d => cyclotomic d ℤ).prod := by
  rw [e7One_wordMat]
  exact charpoly_of_basis e7OneMat e7OneBasis e7OneBasisInv [1, 1, 1, 1, 1, 1, 1]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem exists_elemAbelian_E7_one
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 1) :
    ∃ E : Subgroup (adjointGroup Tag.E7 K), IsElemAbelian p E ∧ Nat.card E = p ^ 7 := by
  have h := exists_elemAbelian_of_blocks 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp hp3
    (IsWeylMatrix.of_word Tag.E7 e7OneWord) [1, 1, 1, 1, 1, 1, 1]
    e7One_charpoly e7One_pow he (by norm_num) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
