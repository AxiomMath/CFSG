module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcMat
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Two
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Three

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
open scoped commutatorElement

set_option linter.unusedSectionVars false


namespace E8Data

@[expose] def q12a : List (Fin Tag.E8.rank) :=
  [5, 6, 7, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 2, 1, 3, 0, 2, 0]

@[expose] def q12b : List (Fin Tag.E8.rank) :=
  [0, 2, 3, 4, 5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 1]

@[expose] def q12c : List (Fin Tag.E8.rank) :=
  [4, 3, 2, 1, 3, 4, 5, 6, 7, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3, 4, 1, 3, 1, 0]

@[expose] def q12d : List (Fin Tag.E8.rank) :=
  [7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 4]

@[expose] def q12LA : List (List ℤ) :=
  [[-1, 1, 0, 0, 0, 1, -1, -1], [-1, 0, -1, 1, 0, 2, -2, -1], [-1, 1, -1, 1, -1, 3, -2, -2], [-1, 1, -2, 1, 0, 4, -3, -3], [0, 1, -2, 1, 0, 3, -3, -2], [0, 1, -2, 1, 0, 2, -2, -2], [0, 1, -2, 1, 0, 1, -1, -1], [0, 0, -1, 1, 0, 0, 0, -1]]

@[expose] def q12LAi : List (List ℤ) :=
  [[0, -1, 0, 0, 2, -2, 0, 1], [1, -1, 0, 0, 2, -3, 1, 1], [1, -1, 0, 0, 3, -4, 0, 2], [1, -1, 0, 0, 4, -6, 1, 3], [1, -1, -1, 1, 3, -5, 1, 2], [0, -1, 0, 1, 2, -4, 1, 1], [0, -1, 0, 1, 1, -3, 1, 1], [0, 0, 0, 0, 1, -2, 1, 0]]

@[expose] def q12LB : List (List ℤ) :=
  [[1, -1, 0, 0, -1, 1, 1, -1], [1, -1, 1, -1, -1, 1, 2, -1], [2, -2, 1, -1, -1, 1, 2, -1], [2, -2, 2, -2, -2, 2, 3, -1], [1, -2, 2, -2, -1, 2, 2, -1], [1, -2, 1, -1, -1, 2, 1, 0], [1, -1, 1, -1, -1, 2, 0, 0], [1, 0, 0, -1, 0, 1, 0, 0]]

@[expose] def q12LBi : List (List ℤ) :=
  [[-1, 2, 1, -1, -1, 0, 1, 0], [-1, 3, 0, -1, -1, 0, 1, 0], [-2, 4, 1, -2, -1, 0, 2, -1], [-2, 6, 1, -3, -2, 1, 2, -1], [-2, 5, 1, -3, -1, 1, 1, 0], [-1, 4, 0, -2, -1, 1, 1, 0], [-1, 3, 0, -1, -1, 1, 0, 0], [-1, 1, 0, 0, -1, 1, 0, 0]]

@[expose] def q12LC : List (List ℤ) :=
  [[0, -1, 1, 0, 0, 0, -1, 2], [0, -1, 2, -1, 0, 0, -1, 3], [-1, -1, 3, -1, 0, 0, -2, 4], [-1, -2, 4, -1, -1, 1, -3, 6], [0, -1, 3, -1, -1, 1, -3, 5], [0, 0, 2, -1, -1, 1, -2, 4], [0, 0, 2, -1, -1, 1, -1, 2], [0, 0, 1, -1, 0, 1, -1, 1]]

@[expose] def q12LCi : List (List ℤ) :=
  [[2, 0, 0, -1, 0, 0, 1, 0], [2, -1, 1, -1, -1, 1, 1, 0], [3, -1, 1, -1, -1, 0, 2, 0], [5, -2, 1, -1, -2, 1, 2, 0], [4, -1, 1, -1, -2, 1, 1, 1], [3, -1, 0, 0, -2, 1, 1, 1], [2, 0, 0, 0, -2, 1, 1, 0], [1, 0, 0, 0, -1, 1, 0, 0]]

@[expose] def q12LD : List (List ℤ) :=
  [[1, 0, 1, 0, -1, -1, 1, 0], [2, 0, 0, 1, -1, -2, 1, 0], [2, 1, 1, 0, -1, -3, 2, 0], [3, 0, 1, 1, -1, -5, 3, 0], [3, 0, 0, 1, -1, -4, 3, 0], [3, 0, 0, 0, 0, -3, 2, 0], [2, 0, 0, 0, 0, -2, 2, -1], [1, 0, 0, 0, 0, -1, 1, -1]]

@[expose] def q12LDi : List (List ℤ) :=
  [[0, 1, 0, 0, -1, 0, 2, -2], [-1, 1, 1, 0, -1, -1, 3, -3], [0, 1, 0, 1, -2, -1, 4, -4], [-1, 2, 0, 1, -2, -2, 6, -6], [-1, 1, 0, 1, -2, -1, 5, -5], [0, 1, 0, 0, -1, -1, 4, -4], [0, 0, 0, 0, 0, -1, 3, -3], [0, 0, 0, 0, 0, 0, 1, -2]]

theorem q12_a : wordMat Tag.E8 q12a = toMat Tag.E8.rank q12LA :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem q12_ai : wordMat Tag.E8 q12a.reverse = toMat Tag.E8.rank q12LAi :=
  wordMat_reverse_eq q12_a (by decide +kernel)

theorem q12_b : wordMat Tag.E8 q12b = toMat Tag.E8.rank q12LB :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem q12_bi : wordMat Tag.E8 q12b.reverse = toMat Tag.E8.rank q12LBi :=
  wordMat_reverse_eq q12_b (by decide +kernel)

theorem q12_c : wordMat Tag.E8 q12c = toMat Tag.E8.rank q12LC :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem q12_ci : wordMat Tag.E8 q12c.reverse = toMat Tag.E8.rank q12LCi :=
  wordMat_reverse_eq q12_c (by decide +kernel)

theorem q12_d : wordMat Tag.E8 q12d = toMat Tag.E8.rank q12LD :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem q12_di : wordMat Tag.E8 q12d.reverse = toMat Tag.E8.rank q12LDi :=
  wordMat_reverse_eq q12_d (by decide +kernel)

theorem q12_dc :
    wordMat Tag.E8 (cw (cw q12a q12b) (cw q12c q12d)) =
      (-1 : ℤ) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) := by
  have h := dc_eq_smul_pow (w := ([] : List (Fin Tag.E8.rank))) q12_a q12_ai q12_b q12_bi q12_c q12_ci q12_d q12_di (W := lid Tag.E8.rank) (s := -1) (k := 0)
    (by rw [wordMat_nil, toMat_lid]) (by decide +kernel)
  rwa [pow_zero] at h

theorem wordMat_e8TwoWord :
    wordMat Tag.E8 e8TwoWord = (-1 : ℤ) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) := by
  have h : wordMat Tag.E8 e8TwoWord =
      toMat Tag.E8.rank (lsmul Tag.E8.rank (-1) (lid Tag.E8.rank)) :=
    wordMat_eq_toMat _ _ (by decide +kernel)
  rw [h, toMat_lsmul, toMat_lid]

@[expose] def r3a : List (Fin Tag.E8.rank) :=
  [5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 2, 1, 3, 4, 5, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3]

@[expose] def r3b : List (Fin Tag.E8.rank) :=
  [4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 1, 3, 4, 0, 2, 1, 3, 1]

@[expose] def r3c : List (Fin Tag.E8.rank) :=
  [0, 2, 1, 3, 4, 5, 6, 7, 3, 0, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 2, 3, 4, 2, 1, 3, 2]

@[expose] def r3d : List (Fin Tag.E8.rank) :=
  [6, 7, 5, 6, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 0, 2, 3, 4, 0, 2, 1, 3, 0, 2]

@[expose] def r3LA : List (List ℤ) :=
  [[1, 1, 0, -2, 1, 0, 1, 0], [1, 1, 1, -3, 1, 1, 1, -1], [2, 1, 0, -3, 1, 1, 2, -1], [2, 2, 1, -5, 1, 2, 3, -2], [1, 1, 1, -4, 1, 2, 2, -1], [1, 0, 1, -3, 1, 1, 2, -1], [0, 0, 1, -2, 1, 0, 2, -1], [0, 0, 1, -1, 0, 0, 1, 0]]

@[expose] def r3LAi : List (List ℤ) :=
  [[-1, 1, 2, -1, 0, -1, 0, 1], [-1, 1, 2, -1, 1, -3, 1, 1], [-2, 2, 3, -2, 1, -3, 1, 2], [-3, 2, 5, -3, 2, -5, 2, 2], [-2, 2, 4, -3, 2, -4, 2, 1], [-2, 1, 3, -2, 2, -3, 1, 1], [-1, 0, 2, -1, 1, -2, 1, 1], [0, 0, 1, -1, 1, -1, 0, 1]]

@[expose] def r3LB : List (List ℤ) :=
  [[1, -1, 1, -1, 1, 0, -1, 1], [1, -2, 1, -1, 2, -1, 0, 1], [1, -3, 2, -1, 2, -1, -1, 2], [2, -4, 2, -1, 3, -2, -1, 3], [2, -4, 1, 0, 2, -1, -1, 2], [1, -3, 1, 0, 1, 0, -1, 2], [1, -2, 0, 0, 1, 0, -1, 2], [0, -1, 0, 0, 1, 0, -1, 1]]

@[expose] def r3LBi : List (List ℤ) :=
  [[1, 0, -2, 1, 0, 1, -1, 0], [1, 0, -3, 2, -1, 2, -2, 1], [1, 0, -3, 2, -1, 3, -3, 1], [1, 0, -5, 3, -1, 4, -4, 2], [1, 1, -4, 2, -1, 3, -3, 2], [1, 1, -3, 1, -1, 3, -2, 1], [0, 1, -2, 1, -1, 2, -1, 0], [0, 0, -1, 1, -1, 1, 0, 0]]

@[expose] def r3LC : List (List ℤ) :=
  [[2, 0, -1, 0, 1, -1, 0, 0], [2, 0, -2, 0, 2, -1, 0, 0], [3, 0, -2, 0, 2, -1, -1, 1], [4, 0, -3, 0, 3, -2, 0, 1], [4, 0, -3, 0, 2, -1, 0, 1], [3, 0, -2, 0, 1, 0, 0, 0], [2, 1, -1, -1, 1, 0, 0, 0], [1, 1, -1, 0, 0, 0, 0, 0]]

@[expose] def r3LCi : List (List ℤ) :=
  [[0, -1, 0, 1, -1, 1, 0, 0], [-1, -1, 0, 2, -2, 1, 0, 1], [-1, -2, 0, 3, -3, 2, 0, 0], [-2, -2, 0, 4, -4, 3, -1, 1], [-2, -1, 0, 3, -3, 2, 0, 0], [-2, -1, 0, 2, -2, 2, 0, 0], [-1, -1, -1, 2, -1, 1, 0, 0], [-1, -1, 0, 1, 0, 0, 0, 0]]

@[expose] def r3LD : List (List ℤ) :=
  [[1, 0, -1, 0, 1, -2, 2, 0], [1, 1, -2, 0, 1, -2, 3, -1], [2, 1, -2, 0, 1, -3, 4, -1], [2, 1, -3, 0, 2, -4, 6, -2], [2, 1, -2, -1, 2, -3, 5, -2], [2, 0, -2, 0, 1, -2, 4, -2], [1, 0, -1, 0, 1, -2, 3, -2], [0, 0, 0, 0, 0, -1, 2, -1]]

@[expose] def r3LDi : List (List ℤ) :=
  [[-1, -2, 1, 1, 0, 0, 0, -1], [-2, -2, 1, 2, 0, -1, 0, -1], [-2, -4, 1, 3, 0, -1, 0, -1], [-3, -5, 1, 5, -1, -1, 0, -2], [-2, -4, 0, 4, 0, -1, 0, -2], [-2, -3, 0, 3, 0, 0, -1, -1], [-1, -2, 0, 2, 0, 0, -1, 0], [0, -1, 0, 1, 0, 0, -1, 0]]

@[expose] def r3LW : List (List ℤ) :=
  [[-2, 0, 0, 0, 0, 1, 0, 0], [-2, 0, 0, -1, 1, 1, 0, 0], [-3, 0, -1, 0, 1, 1, 0, 0], [-4, 1, -1, -1, 1, 2, 0, 0], [-3, 0, -1, 0, 0, 2, 0, 0], [-3, 0, 0, 0, 0, 1, 0, 0], [-2, 0, 0, 0, 0, 1, 0, -1], [-1, 0, 0, 0, 0, 0, 1, -1]]

theorem r3_a : wordMat Tag.E8 r3a = toMat Tag.E8.rank r3LA :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r3_ai : wordMat Tag.E8 r3a.reverse = toMat Tag.E8.rank r3LAi :=
  wordMat_reverse_eq r3_a (by decide +kernel)

theorem r3_b : wordMat Tag.E8 r3b = toMat Tag.E8.rank r3LB :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r3_bi : wordMat Tag.E8 r3b.reverse = toMat Tag.E8.rank r3LBi :=
  wordMat_reverse_eq r3_b (by decide +kernel)

theorem r3_c : wordMat Tag.E8 r3c = toMat Tag.E8.rank r3LC :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r3_ci : wordMat Tag.E8 r3c.reverse = toMat Tag.E8.rank r3LCi :=
  wordMat_reverse_eq r3_c (by decide +kernel)

theorem r3_d : wordMat Tag.E8 r3d = toMat Tag.E8.rank r3LD :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r3_di : wordMat Tag.E8 r3d.reverse = toMat Tag.E8.rank r3LDi :=
  wordMat_reverse_eq r3_d (by decide +kernel)

theorem r3_w : wordMat Tag.E8 e8ThreeWord = toMat Tag.E8.rank r3LW :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r3_dc :
    wordMat Tag.E8 (cw (cw r3a r3b) (cw r3c r3d)) =
      (-1 : ℤ) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) := by
  have h := dc_eq_smul_pow (w := ([] : List (Fin Tag.E8.rank))) r3_a r3_ai r3_b r3_bi r3_c r3_ci r3_d r3_di (W := lid Tag.E8.rank) (s := -1) (k := 0)
    (by rw [wordMat_nil, toMat_lid]) (by decide +kernel)
  rwa [pow_zero] at h

theorem r3_comm_a :
    wordMat Tag.E8 r3a * wordMat Tag.E8 e8ThreeWord = wordMat Tag.E8 e8ThreeWord * wordMat Tag.E8 r3a :=
  comm_of_lists r3_a r3_w (by decide +kernel)

theorem r3_comm_b :
    wordMat Tag.E8 r3b * wordMat Tag.E8 e8ThreeWord = wordMat Tag.E8 e8ThreeWord * wordMat Tag.E8 r3b :=
  comm_of_lists r3_b r3_w (by decide +kernel)

theorem r3_comm_c :
    wordMat Tag.E8 r3c * wordMat Tag.E8 e8ThreeWord = wordMat Tag.E8 e8ThreeWord * wordMat Tag.E8 r3c :=
  comm_of_lists r3_c r3_w (by decide +kernel)

theorem r3_comm_d :
    wordMat Tag.E8 r3d * wordMat Tag.E8 e8ThreeWord = wordMat Tag.E8 e8ThreeWord * wordMat Tag.E8 r3d :=
  comm_of_lists r3_d r3_w (by decide +kernel)

end E8Data

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
