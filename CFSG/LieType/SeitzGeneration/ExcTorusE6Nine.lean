module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e6NineWord : List (Fin Tag.E6.rank) :=
  [0, 3, 2, 4, 3, 1, 5, 4]

@[expose] def e6NineMat : List (List ℤ) :=
  [[0, -1, 0, 1, -1, 1], [0, -1, 0, 1, 0, 0], [1, -1, 0, 1, -1, 1], [1, -2, 0, 2, -1, 0],
   [0, -1, 1, 1, -1, 0], [0, 0, 0, 1, -1, 0]]

@[expose] def e6NineBasis : List (List ℤ) :=
  [[0, 0, 0, 1, 1, 0], [-1, 1, 1, 0, 0, 1], [0, 0, 0, 1, 2, 1], [0, 2, 1, 0, 1, 2],
   [0, 1, 0, 0, 1, 2], [-1, 0, 1, 1, 0, 0]]

@[expose] def e6NineBasisInv : List (List ℤ) :=
  [[-1, -2, 0, 1, 0, 1], [2, 1, -1, 0, 0, -1], [-2, -1, 1, 1, -1, 1], [1, -1, -1, 0, 1, 1],
   [0, 1, 1, 0, -1, -1], [-1, -1, 0, 0, 1, 1]]

theorem e6Nine_wordMat :
    wordMat Tag.E6 e6NineWord = toMat Tag.E6.rank e6NineMat :=
  wordMat_eq_toMat Tag.E6 _ (by decide +kernel)

theorem e6Nine_pow : (wordMat Tag.E6 e6NineWord) ^ 9 = 1 := by
  rw [e6Nine_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E6.rank) (by decide +kernel)

theorem e6Nine_charpoly :
    (wordMat Tag.E6 e6NineWord).charpoly =
      ([9].map fun d => cyclotomic d ℤ).prod := by
  rw [e6Nine_wordMat]
  exact charpoly_of_basis e6NineMat e6NineBasis e6NineBasisInv [9]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E6_nine
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 9) :
    SylowTorus (adjointGroup Tag.E6 K) p 1 :=
  sylowTorus_of_blocks' 3 (Or.inl ⟨rfl, rfl⟩) K hp
    (IsWeylMatrix.of_word Tag.E6 e6NineWord) [9] e6Nine_charpoly
    e6Nine_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
