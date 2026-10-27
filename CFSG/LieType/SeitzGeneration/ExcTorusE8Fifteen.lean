module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e8FifteenWord : List (Fin Tag.E8.rank) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7]

@[expose] def e8FifteenMat : List (List ℤ) :=
  [[0, 0, 1, 0, 0, 0, -1, 0], [1, 1, 0, 0, 0, 0, -1, 0], [0, 1, 1, 0, 0, 0, -1, -1],
   [1, 1, 1, 0, 0, 0, -1, -1], [0, 1, 1, 0, 0, 0, -1, 0], [0, 0, 0, 1, 0, 0, -1, 0],
   [0, 0, 0, 0, 1, 0, -1, 0], [0, 0, 0, 0, 0, 1, -1, 0]]

@[expose] def e8FifteenBasis : List (List ℤ) :=
  [[0, 1, 0, 0, 0, 1, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0], [0, 1, 0, 1, 1, 1, 0, 0],
   [0, 1, 1, 1, 1, 1, 1, 0], [0, 1, 1, 1, 1, 1, 0, 0], [0, 1, 0, 1, 0, 1, 0, 1],
   [-1, 1, 0, 1, 0, 1, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0]]

@[expose] def e8FifteenBasisInv : List (List ℤ) :=
  [[1, 1, 1, 0, -1, 0, -1, -1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, -1, 0, 1, 0, 0, 0],
   [0, 1, 1, 0, -1, 0, 0, -1], [-1, -1, 0, 0, 1, 0, 0, 1], [1, 0, 0, 0, 0, 0, 0, -1],
   [0, 0, 0, 1, -1, 0, 0, 0], [-1, -1, -1, 0, 1, 1, 0, 1]]

theorem e8Fifteen_wordMat :
    wordMat Tag.E8 e8FifteenWord = toMat Tag.E8.rank e8FifteenMat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8Fifteen_pow : (wordMat Tag.E8 e8FifteenWord) ^ 15 = 1 := by
  rw [e8Fifteen_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8Fifteen_charpoly :
    (wordMat Tag.E8 e8FifteenWord).charpoly =
      ([15].map fun d => cyclotomic d ℤ).prod := by
  rw [e8Fifteen_wordMat]
  exact charpoly_of_basis e8FifteenMat e8FifteenBasis e8FifteenBasisInv [15]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E8_fifteen
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 15) :
    SylowTorus (adjointGroup Tag.E8 K) p 1 :=
  sylowTorus_of_blocks' 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E8 e8FifteenWord) [15] e8Fifteen_charpoly
    e8Fifteen_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
