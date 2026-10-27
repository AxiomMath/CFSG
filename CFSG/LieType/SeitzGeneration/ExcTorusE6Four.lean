module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e6FourWord : List (Fin Tag.E6.rank) :=
  [3, 1, 4, 3, 1, 2]

@[expose] def e6FourMat : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0], [1, 0, -1, 0, 1, 0], [1, 0, -1, 1, 0, 0], [2, 0, -2, 1, 0, 1],
   [1, -1, -1, 1, 0, 1], [0, 0, 0, 0, 0, 1]]

@[expose] def e6FourBasis : List (List ℤ) :=
  [[2, 0, 1, 1, 0, 0], [1, -1, -1, 2, -1, -1], [2, -1, 1, -2, 0, 0], [2, -2, -2, -3, 0, -1],
   [1, -2, 2, -2, -1, 0], [0, -2, -1, -1, -1, -1]]

@[expose] def e6FourBasisInv : List (List ℤ) :=
  [[-1, 1, 1, 0, 0, -1], [-5, 3, 8, -3, -3, 0], [1, -1, 1, -1, -1, 2], [2, -1, -3, 1, 1, 0],
   [7, -5, -7, 2, 1, 3], [0, 1, -7, 4, 5, -6]]

theorem e6Four_wordMat : wordMat Tag.E6 e6FourWord = toMat Tag.E6.rank e6FourMat :=
  wordMat_eq_toMat Tag.E6 _ (by decide +kernel)

theorem e6Four_pow : (wordMat Tag.E6 e6FourWord) ^ 4 = 1 := by
  rw [e6Four_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E6.rank) (by decide +kernel)

theorem e6Four_charpoly :
    (wordMat Tag.E6 e6FourWord).charpoly = ([1, 1, 4, 4].map fun d => cyclotomic d ℤ).prod := by
  rw [e6Four_wordMat]
  exact charpoly_of_basis e6FourMat e6FourBasis e6FourBasisInv [1, 1, 4, 4]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E6_four
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 4) :
    SylowTorus (adjointGroup Tag.E6 K) p 2 :=
  sylowTorus_of_blocks' 3 (Or.inl ⟨rfl, rfl⟩) K hp
    (IsWeylMatrix.of_word Tag.E6 e6FourWord) [1, 1, 4, 4] e6Four_charpoly
    e6Four_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
