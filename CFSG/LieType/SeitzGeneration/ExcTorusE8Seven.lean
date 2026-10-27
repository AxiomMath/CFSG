module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e8SevenWord : List (Fin Tag.E8.rank) :=
  [0, 2, 3, 4, 5, 6]

@[expose] def e8SevenMat : List (List ℤ) :=
  [[0, 1, 0, 0, 0, 0, -1, 1], [0, 1, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, -1, 1],
   [0, 1, 1, 0, 0, 0, -1, 1], [0, 0, 0, 1, 0, 0, -1, 1], [0, 0, 0, 0, 1, 0, -1, 1],
   [0, 0, 0, 0, 0, 1, -1, 1], [0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def e8SevenBasis : List (List ℤ) :=
  [[-6, 5, 1, 0, -1, 0, 0, -1], [-11, 9, 0, 0, 0, 0, 0, 0], [-12, 10, 1, 1, -1, -1, 0, -1],
   [-18, 15, 0, 1, 0, -1, -1, -1], [-13, 11, 0, 0, 0, 0, -1, -2], [-8, 7, 0, 0, -1, 0, 0, -2],
   [-3, 3, -1, 0, -1, -1, 0, -1], [2, -1, -1, -1, -1, -1, -1, -1]]

@[expose] def e8SevenBasisInv : List (List ℤ) :=
  [[-18, 4, 9, 0, -9, 18, -18, 9], [-22, 5, 11, 0, -11, 22, -22, 11], [-4, 1, 3, -1, -1, 3, -4, 2],
   [0, -1, -1, 2, -2, 2, -1, 0], [-4, 1, 3, -2, 1, 1, -2, 1], [-1, 0, -1, 2, -3, 4, -3, 1],
   [-2, 1, 2, -2, 1, 0, 0, 0], [-3, 1, 1, 1, -3, 4, -4, 2]]

theorem e8Seven_wordMat : wordMat Tag.E8 e8SevenWord = toMat Tag.E8.rank e8SevenMat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8Seven_pow : (wordMat Tag.E8 e8SevenWord) ^ 7 = 1 := by
  rw [e8Seven_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8Seven_charpoly :
    (wordMat Tag.E8 e8SevenWord).charpoly = ([1, 1, 7].map fun d => cyclotomic d ℤ).prod := by
  rw [e8Seven_wordMat]
  exact charpoly_of_basis e8SevenMat e8SevenBasis e8SevenBasisInv [1, 1, 7]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E8_seven
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 7) :
    SylowTorus (adjointGroup Tag.E8 K) p 1 :=
  sylowTorus_of_blocks' 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E8 e8SevenWord) [1, 1, 7] e8Seven_charpoly
    e8Seven_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
