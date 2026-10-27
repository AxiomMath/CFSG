module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e6FiveWord : List (Fin Tag.E6.rank) :=
  [2, 0, 4, 3]

@[expose] def e6FiveMat : List (List ℤ) :=
  [[-1, 0, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0], [-1, 1, 1, -1, 1, 0], [0, 1, 1, -1, 1, 0],
   [0, 1, 1, -1, 0, 1], [0, 0, 0, 0, 0, 1]]

@[expose] def e6FiveBasis : List (List ℤ) :=
  [[2, -1, 0, -1, 0, -1], [9, -5, -1, -1, -1, -1], [4, -2, -1, -1, -1, -1],
   [6, -3, -1, -1, -2, -1], [-1, 1, 0, -1, -1, 0], [-8, 5, 0, 0, 0, 0]]

@[expose] def e6FiveBasisInv : List (List ℤ) :=
  [[0, 5, -5, 0, 0, 3], [0, 8, -8, 0, 0, 5], [1, 0, -2, 1, 0, 0], [0, 1, -2, 1, -1, 1],
   [0, 2, -1, -1, 0, 1], [-1, 1, 0, -1, 1, 0]]

theorem e6Five_wordMat : wordMat Tag.E6 e6FiveWord = toMat Tag.E6.rank e6FiveMat :=
  wordMat_eq_toMat Tag.E6 _ (by decide +kernel)

theorem e6Five_pow : (wordMat Tag.E6 e6FiveWord) ^ 5 = 1 := by
  rw [e6Five_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E6.rank) (by decide +kernel)

theorem e6Five_charpoly :
    (wordMat Tag.E6 e6FiveWord).charpoly = ([1, 1, 5].map fun d => cyclotomic d ℤ).prod := by
  rw [e6Five_wordMat]
  exact charpoly_of_basis e6FiveMat e6FiveBasis e6FiveBasisInv [1, 1, 5]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E6_five
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 5) :
    SylowTorus (adjointGroup Tag.E6 K) p 1 :=
  sylowTorus_of_blocks' 3 (Or.inl ⟨rfl, rfl⟩) K hp
    (IsWeylMatrix.of_word Tag.E6 e6FiveWord) [1, 1, 5] e6Five_charpoly
    e6Five_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
