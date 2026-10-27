module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e8EighteenWord : List (Fin Tag.E8.rank) :=
  [7, 1, 6, 3, 0, 4, 2, 5, 4]

@[expose] def e8EighteenMat : List (List ℤ) :=
  [[0, 0, -1, 1, 0, 0, 0, 0], [1, 0, -1, 1, 0, -1, 1, 0], [1, 0, -1, 1, 0, 0, 0, 0],
   [1, 1, -1, 1, 0, -1, 1, 0], [0, 0, 0, 1, 0, -1, 1, 0], [0, 0, 0, 1, -1, 0, 1, 0],
   [0, 0, 0, 1, -1, 0, 0, 1], [0, 0, 0, 1, -1, 0, 0, 0]]

@[expose] def e8EighteenBasis : List (List ℤ) :=
  [[-2, 1, 0, 0, -1, 0, -1, -1], [-3, 2, -1, 0, -1, -1, -1, -1], [-4, 2, 0, 0, -1, -1, -1, -2],
   [-6, 3, 0, -1, -1, -2, -2, -2], [-5, 3, 0, 0, -1, -1, -2, -1], [-3, 2, 0, 0, -1, -1, -2, -1],
   [-2, 1, 0, 0, -1, -1, -1, -1], [-1, 1, 0, 0, -1, 0, -1, 0]]

@[expose] def e8EighteenBasisInv : List (List ℤ) :=
  [[-1, 0, 1, 0, -1, 1, -1, 1], [-2, 0, 2, 0, -1, 1, -2, 2], [-1, -1, 1, 0, 0, 0, 0, 1],
   [0, 0, 0, -1, 1, 0, 1, -1], [0, 0, 0, 0, 0, 1, -1, -1], [1, 0, 0, 0, 0, 0, -1, 0],
   [-1, 0, 1, 0, 0, -1, 0, 1], [0, 0, -1, 0, 1, -1, 1, 0]]

theorem e8Eighteen_wordMat : wordMat Tag.E8 e8EighteenWord = toMat Tag.E8.rank e8EighteenMat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8Eighteen_pow : (wordMat Tag.E8 e8EighteenWord) ^ 18 = 1 := by
  rw [e8Eighteen_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8Eighteen_charpoly :
    (wordMat Tag.E8 e8EighteenWord).charpoly = ([1, 2, 18].map fun d => cyclotomic d ℤ).prod := by
  rw [e8Eighteen_wordMat]
  exact charpoly_of_basis e8EighteenMat e8EighteenBasis e8EighteenBasisInv [1, 2, 18]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E8_eighteen
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 18) :
    SylowTorus (adjointGroup Tag.E8 K) p 1 :=
  sylowTorus_of_blocks' 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E8 e8EighteenWord) [1, 2, 18] e8Eighteen_charpoly
    e8Eighteen_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
