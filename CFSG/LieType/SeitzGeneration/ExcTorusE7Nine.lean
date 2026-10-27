module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e7NineWord : List (Fin Tag.E7.rank) :=
  [5, 4, 3, 1, 2, 0, 3, 2]

@[expose] def e7NineMat : List (List ℤ) :=
  [[0, 0, -1, 1, 0, 0, 0], [1, 0, -1, 0, 1, 0, 0], [0, 1, -1, 0, 1, 0, 0], [0, 0, -1, 0, 2, 0, 0],
   [0, 0, -1, 0, 1, 1, 0], [0, 0, -1, 0, 1, 0, 1], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def e7NineBasis : List (List ℤ) :=
  [[-2, 0, 0, 0, 0, -1, -1], [-3, 0, 0, 0, -1, -1, -2], [-4, 0, 0, 0, -1, -2, -2],
   [-6, 0, 0, 0, -2, -3, -4], [-5, 0, 0, -1, -2, -3, -3], [-4, 0, -1, -1, -2, -2, -2],
   [-3, -1, -1, -1, -1, -1, -1]]

@[expose] def e7NineBasisInv : List (List ℤ) :=
  [[0, -1, -1, 1, 0, 0, 0], [1, 1, 0, -1, 0, 1, -1], [-1, 1, 1, -1, 1, -1, 0],
   [-1, -1, 1, 1, -1, 0, 0], [2, 0, -1, 0, 0, 0, 0], [0, 2, 0, -1, 0, 0, 0],
   [-1, 0, 2, -1, 0, 0, 0]]

theorem e7Nine_wordMat :
    wordMat Tag.E7 e7NineWord = toMat Tag.E7.rank e7NineMat :=
  wordMat_eq_toMat Tag.E7 _ (by decide +kernel)

theorem e7Nine_pow : (wordMat Tag.E7 e7NineWord) ^ 9 = 1 := by
  rw [e7Nine_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7Nine_charpoly :
    (wordMat Tag.E7 e7NineWord).charpoly =
      ([1, 9].map fun d => cyclotomic d ℤ).prod := by
  rw [e7Nine_wordMat]
  exact charpoly_of_basis e7NineMat e7NineBasis e7NineBasisInv [1, 9]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E7_nine
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 9) :
    SylowTorus (adjointGroup Tag.E7 K) p 1 :=
  sylowTorus_of_blocks' 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E7 e7NineWord) [1, 9] e7Nine_charpoly
    e7Nine_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
