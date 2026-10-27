module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e8FourteenWord : List (Fin Tag.E8.rank) :=
  [5, 0, 2, 0, 2, 3, 1, 2, 3, 6, 4]

@[expose] def e8FourteenMat : List (List ℤ) :=
  [[0, 1, 0, 0, -1, 1, 0, 0], [0, 0, 1, 0, -1, 1, 0, 0], [0, 0, 0, 1, -2, 2, 0, 0],
   [1, 0, 0, 1, -2, 2, 0, 0], [0, 0, 0, 1, -1, 1, 0, 0], [0, 0, 0, 1, -1, 1, -1, 1],
   [0, 0, 0, 0, 0, 1, -1, 1], [0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def e8FourteenBasis : List (List ℤ) :=
  [[2, 2, 0, -1, 0, 0, 0, -1], [3, 1, -1, 0, 0, 0, -1, -1], [4, 3, 0, 0, 0, -1, -1, -1],
   [6, 3, 0, 0, -1, -1, -1, -1], [5, 3, 0, 0, 0, -1, -1, -1], [4, 2, 0, 0, 0, -1, -1, 0],
   [3, 1, 0, 0, 0, 0, -1, 0], [2, 1, 0, 0, 0, 0, 0, 0]]

@[expose] def e8FourteenBasisInv : List (List ℤ) :=
  [[0, 0, -1, 0, 1, 0, 0, 0], [0, 0, 2, 0, -2, 0, 0, 1], [0, -1, -1, 0, 2, -1, 1, -1],
   [-1, 0, 1, 0, 0, -1, 0, 1], [0, 0, -1, -1, 2, 0, 0, 0], [0, 0, 1, 0, -1, -1, 1, 1],
   [0, 0, -1, 0, 1, 0, -1, 1], [0, 0, 1, 0, -2, 1, 0, 1]]

theorem e8Fourteen_wordMat : wordMat Tag.E8 e8FourteenWord = toMat Tag.E8.rank e8FourteenMat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8Fourteen_pow : (wordMat Tag.E8 e8FourteenWord) ^ 14 = 1 := by
  rw [e8Fourteen_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8Fourteen_charpoly :
    (wordMat Tag.E8 e8FourteenWord).charpoly = ([1, 2, 14].map fun d => cyclotomic d ℤ).prod := by
  rw [e8Fourteen_wordMat]
  exact charpoly_of_basis e8FourteenMat e8FourteenBasis e8FourteenBasisInv [1, 2, 14]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E8_fourteen
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 14) :
    SylowTorus (adjointGroup Tag.E8 K) p 1 :=
  sylowTorus_of_blocks' 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E8 e8FourteenWord) [1, 2, 14] e8Fourteen_charpoly
    e8Fourteen_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
