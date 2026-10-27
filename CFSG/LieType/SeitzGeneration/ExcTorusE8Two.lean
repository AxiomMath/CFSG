module

public import CFSG.LieType.SeitzGeneration.ExcTorusTors
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e8TwoWord : List (Fin Tag.E8.rank) :=
  [0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5,
   4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7,
   6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3,
   1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7]

@[expose] def e8TwoMat : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0, 0, 0],
   [0, 0, 0, -1, 0, 0, 0, 0], [0, 0, 0, 0, -1, 0, 0, 0], [0, 0, 0, 0, 0, -1, 0, 0],
   [0, 0, 0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, 0, 0, -1]]

@[expose] def e8TwoBasis : List (List ℤ) :=
  [[-1, 1, -2, -2, 2, -1, 0, -1], [2, -1, 1, -2, -1, 1, -2, -1], [-2, -2, 0, 2, 1, 0, 0, -1],
   [0, 1, -1, -2, 1, -2, 2, -1], [-2, -2, 2, 1, 2, 1, 1, 0], [1, 1, -2, -1, -1, 2, 2, 0],
   [1, 1, 0, 1, 0, -2, -1, 0], [1, 2, -2, -2, -1, -1, 0, 0]]

@[expose] def e8TwoBasisInv : List (List ℤ) :=
  [[-75, 67, 99, -91, 363, 76, 199, 441], [137, -122, -181, 166, -662, -138, -362, -805],
   [83, -74, -110, 101, -402, -84, -220, -489], [19, -17, -25, 23, -92, -19, -50, -112],
   [-49, 44, 65, -60, 239, 50, 131, 290], [44, -39, -58, 53, -212, -44, -116, -258],
   [-7, 6, 9, -8, 33, 7, 18, 40], [-135, 120, 178, -164, 653, 136, 357, 794]]

theorem e8Two_wordMat :
    wordMat Tag.E8 e8TwoWord = toMat Tag.E8.rank e8TwoMat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8Two_pow : (wordMat Tag.E8 e8TwoWord) ^ 2 = 1 := by
  rw [e8Two_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8Two_charpoly :
    (wordMat Tag.E8 e8TwoWord).charpoly =
      ([2, 2, 2, 2, 2, 2, 2, 2].map fun d => cyclotomic d ℤ).prod := by
  rw [e8Two_wordMat]
  exact charpoly_of_basis e8TwoMat e8TwoBasis e8TwoBasisInv [2, 2, 2, 2, 2, 2, 2, 2]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem exists_elemAbelian_E8_two
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) :
    ∃ E : Subgroup (adjointGroup Tag.E8 K), IsElemAbelian p E ∧ Nat.card E = p ^ 8 := by
  have h := exists_elemAbelian_of_blocks 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp hp3
    (IsWeylMatrix.of_word Tag.E8 e8TwoWord) [2, 2, 2, 2, 2, 2, 2, 2]
    e8Two_charpoly e8Two_pow he (by norm_num) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
