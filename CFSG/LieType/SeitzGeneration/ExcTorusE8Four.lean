module

public import CFSG.LieType.SeitzGeneration.ExcTorusTors
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e8FourWord : List (Fin Tag.E8.rank) :=
  [1, 4, 3, 1, 2, 3, 4, 5, 4, 3, 1, 2, 3, 4, 5, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 6, 7, 6, 5,
   4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 7, 6, 5, 4, 3, 2, 0]

@[expose] def e8FourMat : List (List ℤ) :=
  [[-2, 0, 0, 0, 1, 0, 0, 0], [-3, 0, 0, 0, 1, 0, 1, -1], [-4, 0, 0, 0, 1, 1, 0, 0],
   [-6, 0, 0, 0, 2, 0, 1, 0], [-5, 0, 0, 0, 2, 0, 0, 0], [-3, 0, -1, 0, 2, 0, 0, 0],
   [-2, 0, 0, -1, 2, 0, 0, 0], [-1, 1, 0, -1, 1, 0, 0, 0]]

@[expose] def e8FourBasis : List (List ℤ) :=
  [[-1, 0, 1, -4, -2, 6, -1, 1], [2, 1, -1, -6, 1, 10, 0, 1], [-2, 3, -2, -5, 0, 8, -1, 2],
   [0, 3, 1, -9, -1, 16, 0, 4], [-2, 1, -2, -9, 2, 14, -1, 3], [1, 1, 1, -5, -2, 10, -1, 2],
   [1, -2, 1, -7, 0, 9, 0, 0], [1, 1, 2, -5, -2, 6, 1, 0]]

@[expose] def e8FourBasisInv : List (List ℤ) :=
  [[18, 12, 1, 10, -12, -18, 2, -11], [15, 11, -18, -9, 16, -1, -22, 12],
   [22, 16, -30, -16, 28, 1, -36, 21], [-32, -21, 1, -15, 17, 30, 0, 16],
   [19, 14, -25, -13, 23, 0, -30, 17], [-26, -17, 0, -13, 15, 25, -1, 14],
   [-43, -30, 32, 8, -19, 17, 38, -12], [20, 12, 17, 26, -35, -32, 22, -30]]

theorem e8Four_wordMat :
    wordMat Tag.E8 e8FourWord = toMat Tag.E8.rank e8FourMat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8Four_pow : (wordMat Tag.E8 e8FourWord) ^ 4 = 1 := by
  rw [e8Four_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8Four_charpoly :
    (wordMat Tag.E8 e8FourWord).charpoly =
      ([4, 4, 4, 4].map fun d => cyclotomic d ℤ).prod := by
  rw [e8Four_wordMat]
  exact charpoly_of_basis e8FourMat e8FourBasis e8FourBasisInv [4, 4, 4, 4]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem exists_elemAbelian_E8_four
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 4) :
    ∃ E : Subgroup (adjointGroup Tag.E8 K), IsElemAbelian p E ∧ Nat.card E = p ^ 4 := by
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_pos hp he (by norm_num)
  have hlt := orderOf_lt_prime hp hpq he
  have h := exists_elemAbelian_of_blocks 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp (by omega)
    (IsWeylMatrix.of_word Tag.E8 e8FourWord) [4, 4, 4, 4]
    e8Four_charpoly e8Four_pow he (by norm_num) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
