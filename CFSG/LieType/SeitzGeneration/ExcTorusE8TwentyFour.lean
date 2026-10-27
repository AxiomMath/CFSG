module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e8TwentyFourWord : List (Fin Tag.E8.rank) :=
  [4, 5, 6, 7, 3, 0, 2, 1, 3, 1]

@[expose] def e8TwentyFourMat : List (List ℤ) :=
  [[0, -1, 0, 0, 1, 0, 0, 0], [0, 0, 1, -1, 1, 0, 0, 0], [1, -1, 0, 0, 1, 0, 0, 0],
   [1, 0, 0, -1, 2, 0, 0, 0], [1, 0, 0, -1, 2, 0, 0, -1], [0, 0, 0, 0, 1, 0, 0, -1],
   [0, 0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 0, 1, -1]]

@[expose] def e8TwentyFourBasis : List (List ℤ) :=
  [[0, 0, 0, -1, 1, -1, 1, -2], [0, 0, 1, -1, 0, -1, 1, -1], [1, 0, 0, -1, 0, 0, 0, -1],
   [1, -1, 1, -1, 0, -1, 0, -1], [0, 0, 0, 0, -1, 0, -1, 0], [-1, 1, -1, 1, -1, 0, -1, 0],
   [0, 0, 0, 0, 0, 0, -1, 0], [-1, 1, -1, 1, -1, 1, -1, 0]]

@[expose] def e8TwentyFourBasisInv : List (List ℤ) :=
  [[-1, 0, 1, 1, -2, 1, 0, 0], [-1, 1, 1, 0, -2, 1, 1, 0], [-1, 1, 0, 1, -2, 0, 1, 1],
   [-1, 0, 0, 2, -3, 1, 0, 1], [0, 0, 0, 0, -1, 0, 1, 0], [0, 0, 0, 0, 0, -1, 0, 1],
   [0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, -1, 1, 0, 0, -1]]

theorem e8TwentyFour_wordMat :
    wordMat Tag.E8 e8TwentyFourWord = toMat Tag.E8.rank e8TwentyFourMat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8TwentyFour_pow : (wordMat Tag.E8 e8TwentyFourWord) ^ 24 = 1 := by
  rw [e8TwentyFour_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8TwentyFour_charpoly :
    (wordMat Tag.E8 e8TwentyFourWord).charpoly =
      ([24].map fun d => cyclotomic d ℤ).prod := by
  rw [e8TwentyFour_wordMat]
  exact charpoly_of_basis e8TwentyFourMat e8TwentyFourBasis e8TwentyFourBasisInv [24]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E8_twentyfour
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 24) :
    SylowTorus (adjointGroup Tag.E8 K) p 1 :=
  sylowTorus_of_blocks' 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E8 e8TwentyFourWord) [24] e8TwentyFour_charpoly
    e8TwentyFour_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
