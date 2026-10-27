module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e7EighteenWord : List (Fin Tag.E7.rank) :=
  [0, 1, 2, 3, 4, 6, 5]

@[expose] def e7EighteenMat : List (List ℤ) :=
  [[0, 1, 0, 0, 0, -1, 1], [0, 0, 1, 0, 0, -1, 1], [1, 1, 0, 0, 0, -1, 1], [0, 1, 1, 0, 0, -1, 1],
   [0, 0, 0, 1, 0, -1, 1], [0, 0, 0, 0, 1, -1, 1], [0, 0, 0, 0, 1, -1, 0]]

@[expose] def e7EighteenBasis : List (List ℤ) :=
  [[0, 0, -1, 0, 0, -1, 0], [1, 0, -1, 0, -1, 0, -1], [0, 0, -1, -1, 0, -1, -1],
   [0, 0, -1, -1, -1, -1, -1], [1, 0, -1, 0, -1, -1, -1], [0, 0, -1, 0, 0, -1, -1],
   [-1, -1, 0, 0, 0, -1, 0]]

@[expose] def e7EighteenBasisInv : List (List ℤ) :=
  [[0, 0, 1, -1, 1, -1, 0], [0, -1, -1, 1, 0, 1, -1], [-1, -1, 0, 0, 1, 0, 0],
   [0, 0, -1, 0, 0, 1, 0], [0, 0, 1, -1, 0, 0, 0], [0, 1, 0, 0, -1, 0, 0], [1, 0, 0, 0, 0, -1, 0]]

theorem e7Eighteen_wordMat :
    wordMat Tag.E7 e7EighteenWord = toMat Tag.E7.rank e7EighteenMat :=
  wordMat_eq_toMat Tag.E7 _ (by decide +kernel)

theorem e7Eighteen_pow : (wordMat Tag.E7 e7EighteenWord) ^ 18 = 1 := by
  rw [e7Eighteen_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E7.rank) (by decide +kernel)

theorem e7Eighteen_charpoly :
    (wordMat Tag.E7 e7EighteenWord).charpoly =
      ([2, 18].map fun d => cyclotomic d ℤ).prod := by
  rw [e7Eighteen_wordMat]
  exact charpoly_of_basis e7EighteenMat e7EighteenBasis e7EighteenBasisInv [2, 18]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E7_eighteen
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 18) :
    SylowTorus (adjointGroup Tag.E7 K) p 1 :=
  sylowTorus_of_blocks' 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E7 e7EighteenWord) [2, 18] e7Eighteen_charpoly
    e7Eighteen_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
