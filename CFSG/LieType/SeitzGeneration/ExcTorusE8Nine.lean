module

public import CFSG.LieType.SeitzGeneration.ExcTorusFam
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE Polynomial

@[expose] def e8NineWord : List (Fin Tag.E8.rank) :=
  [4, 5, 2, 1, 3, 4, 1, 3, 1, 0]

@[expose] def e8NineMat : List (List ℤ) :=
  [[-1, 0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, -1, 1, 0, 0], [-1, 0, 2, -1, 0, 1, 0, 0],
   [0, 0, 2, -1, 0, 1, 0, 0], [0, 0, 2, -1, 0, 0, 1, 0], [0, -1, 1, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def e8NineBasis : List (List ℤ) :=
  [[-2, 2, 1, 0, 1, -1, -1, -2], [-3, 3, 0, 1, 0, 0, -2, -2], [-4, 4, 1, 1, 0, -2, -3, -4],
   [-6, 6, 0, 2, 0, -1, -4, -5], [-5, 5, 0, 1, -1, -1, -4, -3], [-4, 4, 0, 0, -1, -1, -3, -2],
   [-3, 3, -1, -1, -1, -1, -1, -1], [2, -1, -1, -1, -1, -1, -1, -1]]

@[expose] def e8NineBasisInv : List (List ℤ) :=
  [[0, 12, 4, -8, 4, -8, 3, 1], [0, 15, 5, -10, 5, -10, 4, 1], [-1, 4, 2, -2, -2, 1, 0, 0],
   [0, 2, 1, -2, 3, -4, 1, 0], [2, -3, -2, 1, 3, -2, 0, 0], [-1, 1, 0, 1, -4, 4, -1, 0],
   [-1, 4, 2, -2, -1, -1, 1, 0], [1, 1, 0, -2, 4, -4, 1, 0]]

theorem e8Nine_wordMat : wordMat Tag.E8 e8NineWord = toMat Tag.E8.rank e8NineMat :=
  wordMat_eq_toMat Tag.E8 _ (by decide +kernel)

theorem e8Nine_pow : (wordMat Tag.E8 e8NineWord) ^ 9 = 1 := by
  rw [e8Nine_wordMat, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E8.rank) (by decide +kernel)

theorem e8Nine_charpoly :
    (wordMat Tag.E8 e8NineWord).charpoly = ([1, 1, 9].map fun d => cyclotomic d ℤ).prod := by
  rw [e8Nine_wordMat]
  exact charpoly_of_basis e8NineMat e8NineBasis e8NineBasisInv [1, 1, 9]
    (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem sylowTorus_E8_nine
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 9) :
    SylowTorus (adjointGroup Tag.E8 K) p 1 :=
  sylowTorus_of_blocks' 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp
    (IsWeylMatrix.of_word Tag.E8 e8NineWord) [1, 1, 9] e8Nine_charpoly
    e8Nine_pow he (by norm_num) (by decide) (by decide) (by decide)

end CFSG.LieType.SeitzGeneration
