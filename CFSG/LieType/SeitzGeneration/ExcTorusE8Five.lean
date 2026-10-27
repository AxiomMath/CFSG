module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e8FiveWord : List (Fin Tag.E8.rank) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7,
   0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7]

@[expose] def e8FiveMat : List (List ℤ) :=
  [[1, 1, 0, 0, 0, -1, 0, -1], [1, 1, 1, 0, -1, 0, -1, -1], [2, 2, 1, -1, 0, -1, -1, -1],
   [2, 3, 2, -1, -1, -1, -1, -2], [2, 2, 1, 0, -1, -1, -1, -1], [1, 1, 1, 0, 0, -1, -1, -1],
   [1, 1, 0, 0, 0, 0, -1, -1], [1, 0, 0, 0, 0, 0, 0, -1]]

@[expose] def e8FiveBasis : List (List ℤ) :=
  [[-1, -1, 4, 0, 2, 3, -3, -2], [2, -1, -1, 2, -1, 1, 0, -2], [-2, -3, 2, 3, 1, 4, 0, -3],
   [0, -2, 1, 2, 1, 3, -1, -3], [-2, -1, 1, 3, 2, 3, 0, -4], [1, -4, 2, 1, -1, 4, -1, -1],
   [1, -1, 1, 1, 0, 2, -1, -2], [1, -2, 1, 3, -1, 3, 0, -3]]

@[expose] def e8FiveBasisInv : List (List ℤ) :=
  [[-1, -6, -4, 9, -2, -1, -5, 6], [1, 0, -4, 0, 3, 2, -5, 2], [-1, -4, 0, 5, -3, -2, 0, 3],
   [1, -2, -5, 5, 1, 1, -9, 5], [-1, -7, -5, 11, -2, -1, -7, 7], [1, 0, -5, 0, 4, 3, -6, 2],
   [-2, -6, -1, 7, -3, -2, 0, 4], [1, -3, -7, 6, 2, 2, -11, 6]]

theorem e8Five_wordMat : wordMat Tag.E8 e8FiveWord = toMat Tag.E8.rank e8FiveMat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8Five_pow : (wordMat Tag.E8 e8FiveWord) ^ 5 = 1 := by
  rw [e8Five_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8Five_charpoly :
    (wordMat Tag.E8 e8FiveWord).charpoly = ([5, 5].map fun d => cyclotomic d ℤ).prod := by
  rw [e8Five_wordMat]
  exact charpoly_of_basis e8FiveMat e8FiveBasis e8FiveBasisInv [5, 5]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E8_five
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 5) :
    SylowTorus (adjointGroup Tag.E8 K) p 2 :=
  sylowTorus_of_blocks' 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E8 e8FiveWord) [5, 5] e8Five_charpoly
    e8Five_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
