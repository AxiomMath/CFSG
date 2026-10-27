module

public import CFSG.LieType.SeitzGeneration.ExcTorusTors
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e6TwoWord : List (Fin Tag.E6.rank) :=
  [1, 2, 3, 1, 2, 3, 4, 3, 1, 2, 3, 4]

@[expose] def e6TwoMat : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0], [1, -1, 0, 0, 0, 1], [2, 0, -1, 0, 0, 1], [2, 0, 0, -1, 0, 2],
   [1, 0, 0, 0, -1, 2], [0, 0, 0, 0, 0, 1]]

@[expose] def e6TwoBasis : List (List ℤ) :=
  [[10, -6, -2, -2, 1, 0], [2, -1, 1, 1, -1, 1], [7, -4, -2, 0, 1, 1], [4, -2, 1, -1, -2, 1],
   [-1, 1, 1, 2, 2, 0], [-6, 4, 2, -2, -1, -1]]

@[expose] def e6TwoBasisInv : List (List ℤ) :=
  [[-16, -82, -17, 64, 22, -35], [-25, -127, -26, 99, 34, -54], [7, 35, 7, -27, -9, 15],
   [-8, -41, -9, 32, 11, -18], [9, 46, 10, -36, -12, 20], [17, 90, 20, -70, -24, 39]]

theorem e6Two_wordMat :
    wordMat Tag.E6 e6TwoWord = toMat Tag.E6.rank e6TwoMat :=
  wordMat_eq_toMat Tag.E6 _ (by decide +kernel)

theorem e6Two_pow : (wordMat Tag.E6 e6TwoWord) ^ 2 = 1 := by
  rw [e6Two_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E6.rank) (by decide +kernel)

theorem e6Two_charpoly :
    (wordMat Tag.E6 e6TwoWord).charpoly =
      ([1, 1, 2, 2, 2, 2].map fun d => cyclotomic d ℤ).prod := by
  rw [e6Two_wordMat]
  exact charpoly_of_basis e6TwoMat e6TwoBasis e6TwoBasisInv [1, 1, 2, 2, 2, 2]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem exists_elemAbelian_E6_two
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) :
    ∃ E : Subgroup (adjointGroup Tag.E6 K), IsElemAbelian p E ∧ Nat.card E = p ^ 4 := by
  have h := exists_elemAbelian_of_blocks 3 (Or.inl ⟨rfl, rfl⟩) K hp hp3
    (IsWeylMatrix.of_word Tag.E6 e6TwoWord) [1, 1, 2, 2, 2, 2]
    e6Two_charpoly e6Two_pow he (by norm_num) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
