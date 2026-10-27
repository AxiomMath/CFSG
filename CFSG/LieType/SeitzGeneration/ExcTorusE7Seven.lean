module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e7SevenWord : List (Fin Tag.E7.rank) :=
  [6, 5, 4, 3, 2, 0]

@[expose] def e7SevenMat : List (List ℤ) :=
  [[-1, 0, 1, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [-1, 0, 0, 1, 0, 0, 0], [-1, 1, 0, 0, 1, 0, 0],
   [-1, 1, 0, 0, 0, 1, 0], [-1, 1, 0, 0, 0, 0, 1], [-1, 1, 0, 0, 0, 0, 0]]

@[expose] def e7SevenBasis : List (List ℤ) :=
  [[-4, 0, 0, 1, 0, 2, 0], [-7, 1, 1, 1, 1, 1, 1], [-8, 0, 1, 1, 2, 2, 1], [-12, 1, 1, 3, 2, 3, 1],
   [-9, 0, 2, 2, 2, 2, 0], [-6, 1, 1, 2, 1, 1, 0], [-3, 0, 1, 1, 0, 1, -1]]

@[expose] def e7SevenBasisInv : List (List ℤ) :=
  [[2, 0, 0, -2, 1, 2, -2], [2, 0, 2, -3, -1, 4, -1], [4, 1, -1, -4, 3, 3, -4],
   [1, 0, -2, 0, 2, 0, -2], [0, -1, 2, -1, -1, 2, 0], [4, 0, 1, -4, 1, 4, -3],
   [3, 1, -2, -2, 3, 1, -4]]

theorem e7Seven_wordMat :
    wordMat Tag.E7 e7SevenWord = toMat Tag.E7.rank e7SevenMat :=
  wordMat_eq_toMat Tag.E7 _ (by decide +kernel)

theorem e7Seven_pow : (wordMat Tag.E7 e7SevenWord) ^ 7 = 1 := by
  rw [e7Seven_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7Seven_charpoly :
    (wordMat Tag.E7 e7SevenWord).charpoly =
      ([1, 7].map fun d => cyclotomic d ℤ).prod := by
  rw [e7Seven_wordMat]
  exact charpoly_of_basis e7SevenMat e7SevenBasis e7SevenBasisInv [1, 7]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E7_seven
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 7) :
    SylowTorus (adjointGroup Tag.E7 K) p 1 :=
  sylowTorus_of_blocks' 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E7 e7SevenWord) [1, 7] e7Seven_charpoly
    e7Seven_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
