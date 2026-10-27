module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e8TwelveWord : List (Fin Tag.E8.rank) :=
  [4, 3, 1, 5, 4, 3, 2, 6, 5, 4, 3, 1, 2, 7, 6, 5, 4, 3, 2, 0]

@[expose] def e8TwelveMat : List (List ℤ) :=
  [[-1, 0, 1, 0, 0, 0, 0, 0], [-2, 0, 1, 0, 0, 0, 1, 0], [-2, 0, 1, 0, 0, 1, 0, 0],
   [-4, 0, 2, 0, 0, 1, 0, 1], [-4, 0, 2, 0, 0, 1, 0, 0], [-3, 0, 1, 0, 1, 0, 0, 0],
   [-2, 1, 1, -1, 1, 0, 0, 0], [-1, 1, 0, 0, 0, 0, 0, 0]]

@[expose] def e8TwelveBasis : List (List ℤ) :=
  [[-1, -1, 2, 0, 0, -1, 1, 0], [2, 1, 3, 1, 0, -1, 0, 0], [-2, 1, 2, 3, -1, 0, 1, 1],
   [0, 2, 8, 3, 1, -1, 3, 0], [-2, 1, 5, 1, 0, -1, 3, 0], [1, -1, 5, 1, 1, -1, 2, 1],
   [1, 0, 3, -2, 0, -2, 1, -1], [1, 3, 2, 1, 0, 0, 0, -1]]

@[expose] def e8TwelveBasisInv : List (List ℤ) :=
  [[-5, -5, 4, 5, -6, -1, 6, -3], [2, 6, -4, -3, 6, -1, -5, 0], [5, 0, -1, -5, 2, 4, -3, 6],
   [-5, -3, 3, 6, -5, -3, 5, -5], [3, 10, -7, -3, 9, -3, -8, -2], [2, -8, 4, -2, -5, 6, 3, 7],
   [-10, -7, 6, 10, -9, -4, 10, -8], [6, 10, -7, -8, 11, 1, -10, 3]]

theorem e8Twelve_wordMat : wordMat Tag.E8 e8TwelveWord = toMat Tag.E8.rank e8TwelveMat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8Twelve_pow : (wordMat Tag.E8 e8TwelveWord) ^ 12 = 1 := by
  rw [e8Twelve_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8Twelve_charpoly :
    (wordMat Tag.E8 e8TwelveWord).charpoly = ([12, 12].map fun d => cyclotomic d ℤ).prod := by
  rw [e8Twelve_wordMat]
  exact charpoly_of_basis e8TwelveMat e8TwelveBasis e8TwelveBasisInv [12, 12]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E8_twelve
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 12) :
    SylowTorus (adjointGroup Tag.E8 K) p 2 :=
  sylowTorus_of_blocks' 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E8 e8TwelveWord) [12, 12] e8Twelve_charpoly
    e8Twelve_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
