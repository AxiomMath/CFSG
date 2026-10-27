module

public import CFSG.LieType.SeitzGeneration.ExcTorusTors
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e6ThreeWord : List (Fin Tag.E6.rank) :=
  [0, 2, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 5, 4, 3, 1, 2, 3, 4, 5]

@[expose] def e6ThreeMat : List (List ℤ) :=
  [[0, 0, 0, 0, 0, -1], [1, -1, -1, 1, 0, -1], [1, 0, -1, 1, -1, -1], [2, -1, -1, 1, -1, -1],
   [1, -1, 0, 1, -1, -1], [1, 0, 0, 0, 0, -1]]

@[expose] def e6ThreeBasis : List (List ℤ) :=
  [[-1, -1, 1, -1, -1, 0], [2, -2, 1, -3, 0, 0], [-2, 2, 1, 0, -1, 1], [0, -1, -1, 0, 0, 0],
   [-2, -2, -2, 0, -1, 0], [1, -2, 1, 0, 0, -1]]

@[expose] def e6ThreeBasisInv : List (List ℤ) :=
  [[-6, 2, 3, -4, 3, 3], [-3, 1, 1, -4, 2, 1], [3, -1, -1, 3, -2, -1], [-1, 0, 1, 1, 0, 1],
   [12, -4, -6, 10, -7, -6], [3, -1, 0, 7, -3, -1]]

theorem e6Three_wordMat :
    wordMat Tag.E6 e6ThreeWord = toMat Tag.E6.rank e6ThreeMat :=
  wordMat_eq_toMat Tag.E6 _ (by decide +kernel)

theorem e6Three_pow : (wordMat Tag.E6 e6ThreeWord) ^ 3 = 1 := by
  rw [e6Three_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E6.rank) (by decide +kernel)

theorem e6Three_charpoly :
    (wordMat Tag.E6 e6ThreeWord).charpoly =
      ([3, 3, 3].map fun d => cyclotomic d ℤ).prod := by
  rw [e6Three_wordMat]
  exact charpoly_of_basis e6ThreeMat e6ThreeBasis e6ThreeBasisInv [3, 3, 3]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem exists_elemAbelian_E6_three
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 3) :
    ∃ E : Subgroup (adjointGroup Tag.E6 K), IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_pos hp he (by norm_num)
  have hlt := orderOf_lt_prime hp hpq he
  have h := exists_elemAbelian_of_blocks 3 (Or.inl ⟨rfl, rfl⟩) K hp (by omega)
    (IsWeylMatrix.of_word Tag.E6 e6ThreeWord) [3, 3, 3]
    e6Three_charpoly e6Three_pow he (by norm_num) (by decide)
  simpa using h

end CFSG.LieType.SeitzGeneration
