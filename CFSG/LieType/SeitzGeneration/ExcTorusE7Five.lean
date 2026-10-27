module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e7FiveWord : List (Fin Tag.E7.rank) :=
  [0, 2, 3, 4]

@[expose] def e7FiveMat : List (List ℤ) :=
  [[0, 1, 0, 0, -1, 1, 0], [0, 1, 0, 0, 0, 0, 0], [1, 1, 0, 0, -1, 1, 0], [0, 1, 1, 0, -1, 1, 0],
   [0, 0, 0, 1, -1, 1, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def e7FiveBasis : List (List ℤ) :=
  [[0, 2, -3, 0, 0, -1, 0], [-1, 6, -8, -2, -2, -2, -2], [0, 4, -6, -1, 0, -1, -1],
   [0, 6, -9, -1, -1, -1, -1], [1, 2, -4, 0, 1, 0, 1], [2, -2, 1, 2, 2, 2, 2],
   [-2, 1, 1, -1, -1, -1, -1]]

@[expose] def e7FiveBasisInv : List (List ℤ) :=
  [[0, 15, 0, -12, 0, 10, 2], [0, 14, 0, -11, 0, 10, 3], [0, 10, 0, -8, 0, 7, 2],
   [1, -1, 0, 1, -1, 0, 0], [0, -2, 1, 1, 0, -1, 0], [-1, -2, 0, 2, 0, -1, 0],
   [0, -1, -1, 1, 1, -1, 0]]

theorem e7Five_wordMat : wordMat Tag.E7 e7FiveWord = toMat Tag.E7.rank e7FiveMat :=
  wordMat_eq_toMat Tag.E7 _ (by decide +kernel)

theorem e7Five_pow : (wordMat Tag.E7 e7FiveWord) ^ 5 = 1 := by
  rw [e7Five_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7Five_charpoly :
    (wordMat Tag.E7 e7FiveWord).charpoly = ([1, 1, 1, 5].map fun d => cyclotomic d ℤ).prod := by
  rw [e7Five_wordMat]
  exact charpoly_of_basis e7FiveMat e7FiveBasis e7FiveBasisInv [1, 1, 1, 5]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E7_five
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 5) :
    SylowTorus (adjointGroup Tag.E7 K) p 1 :=
  sylowTorus_of_blocks' 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E7 e7FiveWord) [1, 1, 1, 5] e7Five_charpoly
    e7Five_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
