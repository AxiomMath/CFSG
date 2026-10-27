module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e8EightWord : List (Fin Tag.E8.rank) :=
  [0, 1, 2, 3, 2, 0, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 7, 6, 5, 4, 3]

@[expose] def e8EightMat : List (List ℤ) :=
  [[0, 2, 0, -1, 0, 0, 1, -1], [0, 2, 1, -2, 1, -1, 2, -2], [1, 3, 0, -2, 1, -1, 2, -2],
   [0, 4, 1, -3, 2, -2, 3, -3], [0, 3, 1, -2, 1, -2, 3, -2], [0, 2, 1, -1, 0, -1, 2, -2],
   [0, 2, 1, -1, 0, -1, 1, -1], [0, 1, 1, -1, 0, 0, 0, 0]]

@[expose] def e8EightBasis : List (List ℤ) :=
  [[-2, 5, 8, 3, 1, -1, -2, 0], [1, 12, 9, 7, 0, -4, -2, -2], [0, 11, 15, 9, 0, -3, -4, -2],
   [-1, 21, 23, 14, 1, -7, -7, -4], [2, 15, 19, 11, -1, -5, -6, -3],
   [-2, 9, 15, 11, 1, -2, -4, -3], [0, 7, 10, 3, 0, -2, -3, 0], [-2, 2, 2, 1, 0, -1, 0, 1]]

@[expose] def e8EightBasisInv : List (List ℤ) :=
  [[-19, 1, 0, 2, -10, 7, 18, 1], [27, 6, -19, -8, 19, 0, -16, -1],
   [-19, -9, 27, 9, -17, -7, 5, 0], [0, 7, -19, -5, 5, 10, 9, 1], [-38, 1, 2, 5, -21, 13, 35, 2],
   [52, 12, -38, -16, 37, 1, -30, -2], [-35, -17, 52, 17, -32, -14, 8, 0],
   [-2, 13, -35, -9, 8, 19, 19, 2]]

theorem e8Eight_wordMat : wordMat Tag.E8 e8EightWord = toMat Tag.E8.rank e8EightMat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8Eight_pow : (wordMat Tag.E8 e8EightWord) ^ 8 = 1 := by
  rw [e8Eight_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8Eight_charpoly :
    (wordMat Tag.E8 e8EightWord).charpoly = ([8, 8].map fun d => cyclotomic d ℤ).prod := by
  rw [e8Eight_wordMat]
  exact charpoly_of_basis e8EightMat e8EightBasis e8EightBasisInv [8, 8]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E8_eight
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 8) :
    SylowTorus (adjointGroup Tag.E8 K) p 2 :=
  sylowTorus_of_blocks' 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E8 e8EightWord) [8, 8] e8Eight_charpoly
    e8Eight_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
