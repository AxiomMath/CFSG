module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e6SixWord : List (Fin Tag.E6.rank) :=
  [2, 3, 1, 2, 4, 3, 2, 0, 5, 4, 3, 1]

@[expose] def e6SixMat : List (List ℤ) :=
  [[-1, 0, 1, 0, 0, 0], [-1, -1, 1, 0, 0, 1], [-2, -1, 2, 0, 0, 0], [-2, -2, 2, 1, -1, 1],
   [-1, -2, 1, 1, 0, 0], [0, -1, 1, 0, 0, 0]]

@[expose] def e6SixBasis : List (List ℤ) :=
  [[-1, 1, 1, -3, -1, 2], [1, 1, -1, -1, 0, 3], [0, 1, -2, -5, 1, 4], [1, 1, 1, 0, -1, 3],
   [1, 0, -2, 0, 1, 1], [1, -1, 1, -1, 1, 1]]

@[expose] def e6SixBasisInv : List (List ℤ) :=
  [[3, 9, -4, -6, -1, 2], [-4, 7, 1, -3, -8, 0], [-2, 1, 1, 0, -3, 0], [-2, -4, 2, 3, 0, -1],
   [-6, -1, 4, 2, -6, -1], [-1, -6, 2, 4, 2, -1]]

theorem e6Six_wordMat : wordMat Tag.E6 e6SixWord = toMat Tag.E6.rank e6SixMat :=
  wordMat_eq_toMat Tag.E6 _ (by decide +kernel)

theorem e6Six_pow : (wordMat Tag.E6 e6SixWord) ^ 6 = 1 := by
  rw [e6Six_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E6.rank) (by decide +kernel)

theorem e6Six_charpoly :
    (wordMat Tag.E6 e6SixWord).charpoly = ([3, 6, 6].map fun d => cyclotomic d ℤ).prod := by
  rw [e6Six_wordMat]
  exact charpoly_of_basis e6SixMat e6SixBasis e6SixBasisInv [3, 6, 6]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E6_six
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 6) :
    SylowTorus (adjointGroup Tag.E6 K) p 2 :=
  sylowTorus_of_blocks' 3 (Or.inl ⟨rfl, rfl⟩) K hp
    (IsWeylMatrix.of_word Tag.E6 e6SixWord) [3, 6, 6] e6Six_charpoly
    e6Six_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
