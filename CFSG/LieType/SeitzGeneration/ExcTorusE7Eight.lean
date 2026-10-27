module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e7EightWord : List (Fin Tag.E7.rank) :=
  [0, 1, 2, 3, 4]

@[expose] def e7EightMat : List (List ℤ) :=
  [[0, 1, 0, 0, -1, 1, 0], [0, 0, 1, 0, -1, 1, 0], [1, 1, 0, 0, -1, 1, 0], [0, 1, 1, 0, -1, 1, 0],
   [0, 0, 0, 1, -1, 1, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def e7EightBasis : List (List ℤ) :=
  [[-2, 2, -1, 0, 0, -1, -1], [-3, 3, -1, 0, 0, -1, -1], [-4, 4, -2, 0, 0, -1, -2],
   [-6, 6, -3, 0, 0, -1, -2], [-5, 5, -2, -1, 0, -1, -1], [-4, 4, -2, -1, -1, -1, -1],
   [2, -1, -2, 0, 0, 0, 0]]

@[expose] def e7EightBasisInv : List (List ℤ) :=
  [[-5, 5, 2, -2, 0, 0, 1], [-6, 6, 2, -2, 0, 0, 1], [-2, 2, 1, -1, 0, 0, 0],
   [0, 1, -1, 1, -1, 0, 0], [1, -1, 0, 0, 1, -1, 0], [-2, 0, 1, 0, 0, 0, 0],
   [1, 0, -2, 1, 0, 0, 0]]

theorem e7Eight_wordMat : wordMat Tag.E7 e7EightWord = toMat Tag.E7.rank e7EightMat :=
  wordMat_eq_toMat Tag.E7 _ (by decide +kernel)

theorem e7Eight_pow : (wordMat Tag.E7 e7EightWord) ^ 8 = 1 := by
  rw [e7Eight_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7Eight_charpoly :
    (wordMat Tag.E7 e7EightWord).charpoly = ([1, 1, 2, 8].map fun d => cyclotomic d ℤ).prod := by
  rw [e7Eight_wordMat]
  exact charpoly_of_basis e7EightMat e7EightBasis e7EightBasisInv [1, 1, 2, 8]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E7_eight
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 8) :
    SylowTorus (adjointGroup Tag.E7 K) p 1 :=
  sylowTorus_of_blocks' 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E7 e7EightWord) [1, 1, 2, 8] e7Eight_charpoly
    e7Eight_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
