module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e8ThirtyWord : List (Fin Tag.E8.rank) :=
  [0, 1, 2, 3, 4, 5, 6, 7]

@[expose] def e8ThirtyMat : List (List ℤ) :=
  [[0, 1, 0, 0, 0, 0, 0, -1], [0, 0, 1, 0, 0, 0, 0, -1], [1, 1, 0, 0, 0, 0, 0, -1],
   [0, 1, 1, 0, 0, 0, 0, -1], [0, 0, 0, 1, 0, 0, 0, -1], [0, 0, 0, 0, 1, 0, 0, -1],
   [0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 0, 1, -1]]

@[expose] def e8ThirtyBasis : List (List ℤ) :=
  [[0, 0, 1, 0, 0, 1, 0, 1], [0, 0, 1, 0, 1, 0, 1, 1], [0, 0, 1, 1, 0, 1, 1, 1],
   [0, 0, 1, 1, 1, 1, 1, 2], [0, 0, 1, 0, 1, 1, 1, 1], [0, 0, 1, 0, 0, 1, 1, 1],
   [-1, 0, 1, 0, 0, 0, 1, 1], [0, -1, 1, 0, 0, 0, 0, 1]]

@[expose] def e8ThirtyBasisInv : List (List ℤ) :=
  [[0, 1, 0, 0, -1, 1, -1, 0], [1, 1, 0, 0, -1, 0, 0, -1], [1, 1, 1, -1, 0, -1, 0, 0],
   [0, 0, 1, 0, 0, -1, 0, 0], [0, 0, 0, 0, 1, -1, 0, 0], [0, -1, 0, 0, 1, 0, 0, 0],
   [-1, 0, 0, 0, 0, 1, 0, 0], [0, 0, -1, 1, -1, 1, 0, 0]]

theorem e8Thirty_wordMat :
    wordMat Tag.E8 e8ThirtyWord = toMat Tag.E8.rank e8ThirtyMat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8Thirty_pow : (wordMat Tag.E8 e8ThirtyWord) ^ 30 = 1 := by
  rw [e8Thirty_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8Thirty_charpoly :
    (wordMat Tag.E8 e8ThirtyWord).charpoly =
      ([30].map fun d => cyclotomic d ℤ).prod := by
  rw [e8Thirty_wordMat]
  exact charpoly_of_basis e8ThirtyMat e8ThirtyBasis e8ThirtyBasisInv [30]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E8_thirty
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 30) :
    SylowTorus (adjointGroup Tag.E8 K) p 1 :=
  sylowTorus_of_blocks' 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E8 e8ThirtyWord) [30] e8Thirty_charpoly
    e8Thirty_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
