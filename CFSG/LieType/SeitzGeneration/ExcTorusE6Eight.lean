module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e6EightWord : List (Fin Tag.E6.rank) :=
  [1, 4, 3, 2, 0]

@[expose] def e6EightMat : List (List ℤ) :=
  [[-1, 0, 1, 0, 0, 0], [-1, 0, 0, 0, 1, 0], [-1, 0, 0, 1, 0, 0], [-1, 1, 0, 0, 1, 0],
   [-1, 1, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1]]

@[expose] def e6EightBasis : List (List ℤ) :=
  [[2, -1, 0, 0, 0, 0], [3, -2, 0, 0, 1, 1], [4, -2, 0, 0, 0, 1], [6, -3, 0, 0, 1, 2],
   [5, -2, 0, 1, 1, 2], [4, -2, 1, 1, 1, 1]]

@[expose] def e6EightBasisInv : List (List ℤ) :=
  [[1, -1, -1, 1, 0, 0], [1, -2, -2, 2, 0, 0], [-1, -1, 0, 1, -1, 1], [0, 1, 1, -2, 1, 0],
   [1, 0, -2, 1, 0, 0], [-2, 0, 1, 0, 0, 0]]

theorem e6Eight_wordMat :
    wordMat Tag.E6 e6EightWord = toMat Tag.E6.rank e6EightMat :=
  wordMat_eq_toMat Tag.E6 _ (by decide +kernel)

theorem e6Eight_pow : (wordMat Tag.E6 e6EightWord) ^ 8 = 1 := by
  rw [e6Eight_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E6.rank) (by decide +kernel)

theorem e6Eight_charpoly :
    (wordMat Tag.E6 e6EightWord).charpoly =
      ([1, 2, 8].map fun d => cyclotomic d ℤ).prod := by
  rw [e6Eight_wordMat]
  exact charpoly_of_basis e6EightMat e6EightBasis e6EightBasisInv [1, 2, 8]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E6_eight
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 8) :
    SylowTorus (adjointGroup Tag.E6 K) p 1 :=
  sylowTorus_of_blocks' 3 (Or.inl ⟨rfl, rfl⟩) K hp
    (IsWeylMatrix.of_word Tag.E6 e6EightWord) [1, 2, 8] e6Eight_charpoly
    e6Eight_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
