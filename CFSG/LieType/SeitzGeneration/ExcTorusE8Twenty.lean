module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e8TwentyWord : List (Fin Tag.E8.rank) :=
  [7, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 4, 3, 0]

@[expose] def e8TwentyMat : List (List ℤ) :=
  [[0, 1, 0, 0, 0, 0, -1, 1], [0, 0, 1, 0, 0, 0, -1, 1], [0, 1, 1, 0, -1, 1, -2, 2],
   [-1, 1, 2, 0, -1, 1, -2, 2], [0, 1, 1, 0, -1, 1, -1, 1], [0, 1, 1, -1, 0, 1, -1, 1],
   [0, 0, 0, 0, 0, 1, -1, 1], [0, 0, 0, 0, 0, 1, -1, 0]]

@[expose] def e8TwentyBasis : List (List ℤ) :=
  [[0, 1, 1, 1, 2, 1, 1, 1], [0, 1, 2, 2, 2, 2, 1, 1], [0, 2, 3, 2, 3, 2, 1, 2],
   [0, 2, 4, 4, 4, 3, 2, 2], [0, 1, 3, 3, 3, 3, 2, 2], [0, 1, 2, 2, 2, 2, 2, 2],
   [-1, 1, 1, 1, 2, 1, 1, 2], [0, 1, 0, 1, 1, 0, 1, 1]]

@[expose] def e8TwentyBasisInv : List (List ℤ) :=
  [[0, -1, 1, -1, 2, -1, -1, 1], [0, 2, 0, 0, -2, 1, 0, 0], [0, -1, 0, 1, -1, 1, 0, -1],
   [-1, 0, 0, 0, 1, -1, 0, 1], [1, -1, 0, 0, 1, -1, 0, 0], [0, 2, 0, -1, 0, 0, 0, 0],
   [1, 0, -1, 1, -2, 2, 0, -1], [-1, -1, 1, -1, 2, -1, 0, 1]]

theorem e8Twenty_wordMat :
    wordMat Tag.E8 e8TwentyWord = toMat Tag.E8.rank e8TwentyMat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8Twenty_pow : (wordMat Tag.E8 e8TwentyWord) ^ 20 = 1 := by
  rw [e8Twenty_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8Twenty_charpoly :
    (wordMat Tag.E8 e8TwentyWord).charpoly =
      ([20].map fun d => cyclotomic d ℤ).prod := by
  rw [e8Twenty_wordMat]
  exact charpoly_of_basis e8TwentyMat e8TwentyBasis e8TwentyBasisInv [20]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E8_twenty
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 20) :
    SylowTorus (adjointGroup Tag.E8 K) p 1 :=
  sylowTorus_of_blocks' 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E8 e8TwentyWord) [20] e8Twenty_charpoly
    e8Twenty_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
