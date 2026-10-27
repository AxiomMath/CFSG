module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e8TenWord : List (Fin Tag.E8.rank) :=
  [1, 2, 0, 3, 1, 4, 3, 1, 2, 5, 4, 3, 1, 2, 0, 3, 4, 5, 6, 5, 4, 3, 7, 6]

@[expose] def e8TenMat : List (List ℤ) :=
  [[0, 0, 1, -1, 1, 0, 0, -1], [-1, 0, 2, -1, 1, 0, -1, 0], [-1, 0, 3, -2, 1, 1, -1, -1],
   [-2, 0, 4, -2, 1, 1, -1, -1], [-2, 1, 3, -2, 1, 1, -1, -1], [-1, 1, 2, -1, 0, 1, -1, -1],
   [0, 1, 1, -1, 0, 1, -1, 0], [0, 0, 0, 0, 0, 1, -1, 0]]

@[expose] def e8TenBasis : List (List ℤ) :=
  [[-1, -5, -4, -4, 0, -2, -2, -2], [2, -6, -7, -3, 1, -2, -3, -2],
   [-2, -8, -8, -8, 0, -3, -4, -4], [0, -9, -11, -12, 1, -3, -5, -6],
   [-2, -5, -9, -11, 0, -2, -4, -5], [1, -2, -10, -9, 1, -1, -4, -4], [1, 0, -7, -7, 1, 0, -3, -3],
   [1, 0, -2, -3, 1, 0, -1, -1]]

@[expose] def e8TenBasisInv : List (List ℤ) :=
  [[6, 2, -5, -1, 3, -4, 4, -1], [1, -2, 1, 1, -3, 2, 0, -1], [4, 0, -2, 0, 0, -2, 3, -1],
   [-3, -3, 4, 2, -5, 4, -2, -1], [-11, -5, 10, 3, -8, 9, -8, 2], [-4, 4, -1, -2, 6, -4, 0, 2],
   [-8, -1, 4, 1, -1, 5, -7, 2], [4, 7, -7, -5, 11, -8, 3, 3]]

theorem e8Ten_wordMat : wordMat Tag.E8 e8TenWord = toMat Tag.E8.rank e8TenMat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8Ten_pow : (wordMat Tag.E8 e8TenWord) ^ 10 = 1 := by
  rw [e8Ten_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8Ten_charpoly :
    (wordMat Tag.E8 e8TenWord).charpoly = ([10, 10].map fun d => cyclotomic d ℤ).prod := by
  rw [e8Ten_wordMat]
  exact charpoly_of_basis e8TenMat e8TenBasis e8TenBasisInv [10, 10]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E8_ten
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 10) :
    SylowTorus (adjointGroup Tag.E8 K) p 2 :=
  sylowTorus_of_blocks' 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E8 e8TenWord) [10, 10] e8Ten_charpoly
    e8Ten_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
