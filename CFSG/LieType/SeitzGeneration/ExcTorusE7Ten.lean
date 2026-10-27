module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e7TenWord : List (Fin Tag.E7.rank) :=
  [3, 1, 2, 4, 3, 1, 2, 0, 3, 6, 5, 4, 3, 1, 2]

@[expose] def e7TenMat : List (List ℤ) :=
  [[0, 0, -1, 1, 0, 0, 0], [0, -1, -1, 1, 0, 1, 0], [1, 0, -2, 1, 0, 1, 0],
   [1, -1, -3, 2, 0, 1, 1], [1, -1, -2, 2, -1, 1, 1], [1, -1, -1, 1, 0, 0, 1],
   [1, -1, -1, 1, 0, 0, 0]]

@[expose] def e7TenBasis : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 0, -1], [-2, 1, 1, -2, 3, -3, 1], [2, -2, 1, -2, 3, -3, 1],
   [2, -2, 1, -2, 3, -4, 0], [-1, 0, 1, -2, 3, -4, 1], [0, 0, 0, 1, 0, -1, -1],
   [-2, 1, 1, -2, 2, -3, 2]]

@[expose] def e7TenBasisInv : List (List ℤ) :=
  [[-3, 2, -2, 3, -3, 0, 0], [-4, 3, -3, 4, -4, 0, 0], [5, -1, 4, -3, -2, 2, 3],
   [0, 0, 1, -1, 0, 1, 0], [-1, 1, 0, 0, 0, 0, -1], [1, 0, 1, -1, 0, 0, 0], [-1, 0, 0, 0, 0, 0, 0]]

theorem e7Ten_wordMat : wordMat Tag.E7 e7TenWord = toMat Tag.E7.rank e7TenMat :=
  wordMat_eq_toMat Tag.E7 _ (by decide +kernel)

theorem e7Ten_pow : (wordMat Tag.E7 e7TenWord) ^ 10 = 1 := by
  rw [e7Ten_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7Ten_charpoly :
    (wordMat Tag.E7 e7TenWord).charpoly = ([2, 2, 2, 10].map fun d => cyclotomic d ℤ).prod := by
  rw [e7Ten_wordMat]
  exact charpoly_of_basis e7TenMat e7TenBasis e7TenBasisInv [2, 2, 2, 10]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E7_ten
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 10) :
    SylowTorus (adjointGroup Tag.E7 K) p 1 :=
  sylowTorus_of_blocks' 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E7 e7TenWord) [2, 2, 2, 10] e7Ten_charpoly
    e7Ten_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
