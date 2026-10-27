module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcMat
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Five
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Six
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Eight

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
open scoped commutatorElement

set_option linter.unusedSectionVars false


namespace E8Data

@[expose] def r5a : List (Fin Tag.E8.rank) :=
  [5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 3, 4, 5, 6, 0, 2, 3, 4, 5, 4, 2, 3, 0, 2, 1, 3, 4, 1, 3, 0, 2, 0]

@[expose] def r5b : List (Fin Tag.E8.rank) :=
  [6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 1, 3, 4, 5, 0, 2, 1, 3, 4, 2, 0]

@[expose] def r5c : List (Fin Tag.E8.rank) :=
  [1, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 6, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 4, 5, 2, 1, 3, 4, 1, 3, 0]

@[expose] def r5d : List (Fin Tag.E8.rank) :=
  [5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 3, 2, 1, 3, 4, 5, 6, 1, 3, 4, 5, 0, 2, 1, 3, 4, 2, 0]

@[expose] def r5LA : List (List ℤ) :=
  [[-1, 0, 0, 1, -1, 1, 0, -1], [-2, 1, 0, 1, -2, 2, 0, -1], [-3, 0, 0, 2, -2, 2, 0, -1], [-4, 1, -1, 3, -3, 3, 0, -2], [-3, 1, -1, 2, -2, 2, 1, -2], [-2, 0, -1, 2, -2, 2, 1, -2], [-1, 0, -1, 2, -2, 1, 1, -1], [0, 0, -1, 1, -1, 1, 0, 0]]

@[expose] def r5LAi : List (List ℤ) :=
  [[2, 0, 0, -1, 1, -1, 0, 1], [2, 0, 0, -1, 2, -2, 0, 1], [3, 0, 1, -2, 2, -2, 0, 1], [4, -1, 1, -2, 3, -3, 0, 2], [3, -1, 1, -2, 3, -2, -1, 2], [2, 0, 1, -2, 2, -1, -1, 2], [1, 0, 1, -2, 2, -1, 0, 1], [0, 0, 1, -1, 1, -1, 0, 1]]

@[expose] def r5LB : List (List ℤ) :=
  [[-1, 1, 1, 0, -1, 0, 0, -1], [-2, 1, 1, 1, -2, 1, -1, -1], [-2, 2, 2, 0, -2, 1, -1, -2], [-3, 3, 2, 1, -4, 2, -1, -3], [-2, 3, 1, 1, -3, 1, -1, -2], [-2, 2, 1, 1, -2, 0, 0, -2], [-1, 1, 0, 1, -1, 0, 0, -2], [0, 0, 0, 1, -1, 0, 0, -1]]

@[expose] def r5LBi : List (List ℤ) :=
  [[-2, -1, 1, 0, 0, 1, -1, 1], [-3, -1, 1, 0, 0, 2, -1, 0], [-4, -1, 2, 0, -1, 3, -2, 1], [-6, -1, 2, 0, -1, 4, -2, 1], [-5, -1, 2, 0, -1, 3, -1, 0], [-4, -1, 1, 1, -1, 2, -1, 0], [-2, -1, 0, 1, -1, 2, -1, 0], [-1, 0, 0, 0, 0, 1, -1, 0]]

@[expose] def r5LC : List (List ℤ) :=
  [[0, 0, 2, -1, 0, 0, -1, 1], [-1, 0, 3, -1, 0, 0, -2, 1], [-1, 0, 4, -2, 0, 1, -3, 2], [-2, 1, 6, -3, 0, 1, -4, 2], [-2, 0, 5, -2, 0, 1, -3, 1], [-2, 0, 4, -1, -1, 1, -2, 1], [-1, 0, 2, 0, -1, 1, -2, 1], [-1, 0, 1, 0, 0, 0, -1, 1]]

@[expose] def r5LCi : List (List ℤ) :=
  [[2, -1, -1, 0, 1, -1, 1, 0], [2, -2, -2, 1, 1, -1, 1, 1], [3, -2, -2, 0, 2, -1, 1, 1], [4, -3, -3, 0, 3, -2, 2, 2], [3, -3, -2, 0, 3, -2, 1, 2], [2, -3, -1, 0, 2, -1, 1, 1], [2, -2, -1, 0, 1, 0, 0, 1], [1, -1, 0, 0, 0, 0, 0, 1]]

@[expose] def r5LD : List (List ℤ) :=
  [[-1, 1, 1, 0, -1, 1, -1, -1], [-1, 2, 1, 0, -2, 1, 0, -2], [-2, 2, 1, 1, -3, 2, -1, -2], [-2, 4, 1, 1, -4, 2, -1, -3], [-2, 3, 1, 1, -3, 1, 0, -3], [-1, 2, 0, 1, -2, 1, 0, -3], [0, 1, 0, 1, -2, 1, 0, -2], [0, 1, 0, 0, -1, 1, 0, -1]]

@[expose] def r5LDi : List (List ℤ) :=
  [[1, -1, -1, 0, 1, -1, 1, 1], [1, -2, -1, 0, 2, -1, 0, 2], [2, -2, -1, -1, 3, -2, 1, 2], [2, -4, -1, -1, 4, -2, 1, 3], [2, -3, -1, -1, 3, -1, 0, 3], [1, -2, 0, -1, 2, -1, 0, 3], [0, -1, 0, -1, 2, -1, 0, 2], [0, -1, 0, 0, 1, -1, 0, 1]]

@[expose] def r5LW : List (List ℤ) :=
  [[1, 1, 0, 0, 0, -1, 0, -1], [1, 1, 1, 0, -1, 0, -1, -1], [2, 2, 1, -1, 0, -1, -1, -1], [2, 3, 2, -1, -1, -1, -1, -2], [2, 2, 1, 0, -1, -1, -1, -1], [1, 1, 1, 0, 0, -1, -1, -1], [1, 1, 0, 0, 0, 0, -1, -1], [1, 0, 0, 0, 0, 0, 0, -1]]

theorem r5_a : wordMat Tag.E8 r5a = toMat Tag.E8.rank r5LA :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r5_ai : wordMat Tag.E8 r5a.reverse = toMat Tag.E8.rank r5LAi :=
  wordMat_reverse_eq r5_a (by decide +kernel)

theorem r5_b : wordMat Tag.E8 r5b = toMat Tag.E8.rank r5LB :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r5_bi : wordMat Tag.E8 r5b.reverse = toMat Tag.E8.rank r5LBi :=
  wordMat_reverse_eq r5_b (by decide +kernel)

theorem r5_c : wordMat Tag.E8 r5c = toMat Tag.E8.rank r5LC :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r5_ci : wordMat Tag.E8 r5c.reverse = toMat Tag.E8.rank r5LCi :=
  wordMat_reverse_eq r5_c (by decide +kernel)

theorem r5_d : wordMat Tag.E8 r5d = toMat Tag.E8.rank r5LD :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r5_di : wordMat Tag.E8 r5d.reverse = toMat Tag.E8.rank r5LDi :=
  wordMat_reverse_eq r5_d (by decide +kernel)

theorem r5_w : wordMat Tag.E8 e8FiveWord = toMat Tag.E8.rank r5LW :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r5_dc :
    wordMat Tag.E8 (cw (cw r5a r5b) (cw r5c r5d)) =
      (-1 : ℤ) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) := by
  have h := dc_eq_smul_pow (w := ([] : List (Fin Tag.E8.rank))) r5_a r5_ai r5_b r5_bi r5_c r5_ci r5_d r5_di (W := lid Tag.E8.rank) (s := -1) (k := 0)
    (by rw [wordMat_nil, toMat_lid]) (by decide +kernel)
  rwa [pow_zero] at h

theorem r5_comm_a :
    wordMat Tag.E8 r5a * wordMat Tag.E8 e8FiveWord = wordMat Tag.E8 e8FiveWord * wordMat Tag.E8 r5a :=
  comm_of_lists r5_a r5_w (by decide +kernel)

theorem r5_comm_b :
    wordMat Tag.E8 r5b * wordMat Tag.E8 e8FiveWord = wordMat Tag.E8 e8FiveWord * wordMat Tag.E8 r5b :=
  comm_of_lists r5_b r5_w (by decide +kernel)

theorem r5_comm_c :
    wordMat Tag.E8 r5c * wordMat Tag.E8 e8FiveWord = wordMat Tag.E8 e8FiveWord * wordMat Tag.E8 r5c :=
  comm_of_lists r5_c r5_w (by decide +kernel)

theorem r5_comm_d :
    wordMat Tag.E8 r5d * wordMat Tag.E8 e8FiveWord = wordMat Tag.E8 e8FiveWord * wordMat Tag.E8 r5d :=
  comm_of_lists r5_d r5_w (by decide +kernel)

@[expose] def r6a : List (Fin Tag.E8.rank) :=
  [2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 1, 3, 0, 2, 0]

@[expose] def r6b : List (Fin Tag.E8.rank) :=
  [6, 7, 4, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 6, 4, 3, 0, 2, 1, 3, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 2, 1, 3, 0]

@[expose] def r6c : List (Fin Tag.E8.rank) :=
  [0, 2, 1, 3, 4, 5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 2, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 3, 0, 2, 1]

@[expose] def r6d : List (Fin Tag.E8.rank) :=
  [6, 7, 5, 6, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 1]

@[expose] def r6LA : List (List ℤ) :=
  [[-1, 0, 0, 1, 0, 0, -1, -1], [0, 0, -1, 1, 1, 0, -2, -1], [-1, 0, 0, 1, 1, 0, -3, -1], [-1, 0, -1, 2, 2, -1, -4, -1], [-1, 0, -1, 2, 1, 0, -4, 0], [-1, 1, -1, 1, 1, 0, -3, 0], [-1, 0, -1, 1, 1, 0, -2, 0], [-1, 0, 0, 0, 1, 0, -1, 0]]

@[expose] def r6LAi : List (List ℤ) :=
  [[0, 1, -1, 0, 1, 0, -2, 1], [1, 1, -2, 0, 1, 1, -3, 2], [1, 1, -2, 0, 2, 0, -4, 3], [2, 2, -4, 0, 3, 0, -5, 4], [1, 2, -3, 0, 2, 0, -4, 4], [1, 2, -2, -1, 2, 0, -3, 3], [1, 1, -2, 0, 1, 0, -2, 2], [0, 0, -1, 0, 1, 0, -1, 1]]

@[expose] def r6LB : List (List ℤ) :=
  [[0, 1, 1, -1, -1, 1, 1, -1], [-1, 0, 2, -1, -1, 1, 2, -2], [-1, 1, 2, -2, -1, 2, 2, -2], [-2, 1, 4, -3, -2, 3, 3, -3], [-2, 1, 3, -2, -2, 3, 2, -3], [-2, 1, 3, -2, -1, 2, 1, -2], [-1, 1, 2, -2, 0, 1, 1, -2], [-1, 1, 1, -1, 0, 0, 1, -1]]

@[expose] def r6LBi : List (List ℤ) :=
  [[1, 1, 1, -1, -1, 1, 0, -1], [1, 1, 2, -2, -1, 2, -1, 0], [1, 2, 2, -2, -2, 3, -1, -1], [1, 3, 4, -4, -2, 4, -2, -1], [0, 2, 4, -3, -2, 3, -1, -1], [0, 1, 3, -2, -1, 2, -1, -1], [0, 1, 2, -1, -1, 1, -1, 0], [0, 0, 1, 0, -1, 1, -1, 0]]

@[expose] def r6LC : List (List ℤ) :=
  [[1, -1, -1, 1, 0, 1, -2, 0], [1, -1, -2, 2, -1, 2, -3, 1], [1, -2, -2, 3, -1, 2, -4, 1], [2, -2, -4, 4, -1, 3, -6, 2], [2, -1, -3, 3, -1, 2, -5, 2], [2, -1, -2, 2, -1, 2, -4, 2], [1, -1, -1, 1, 0, 1, -3, 2], [0, 0, 0, 0, 0, 1, -2, 1]]

@[expose] def r6LCi : List (List ℤ) :=
  [[0, -2, 0, 1, -1, 2, -1, 0], [-1, -3, 0, 2, -1, 2, -2, 1], [-1, -4, 1, 2, -2, 3, -2, 1], [-2, -6, 1, 4, -3, 4, -3, 1], [-1, -5, 0, 4, -3, 3, -2, 1], [-1, -3, 0, 3, -3, 3, -2, 1], [-1, -2, 0, 2, -2, 2, -1, 0], [-1, -1, 0, 1, -1, 1, 0, 0]]

@[expose] def r6LD : List (List ℤ) :=
  [[1, 0, 0, -1, 0, 0, 1, 1], [1, 0, 0, -1, 0, -1, 3, 0], [2, -1, 0, -1, 0, -1, 3, 1], [2, -1, 0, -1, -1, -1, 5, 1], [2, -1, 0, -1, -1, 0, 4, 0], [1, -1, 1, -1, -1, 0, 3, 0], [1, -1, 0, 0, -1, 0, 2, 0], [0, -1, 0, 0, 0, 0, 1, 0]]

@[expose] def r6LDi : List (List ℤ) :=
  [[-1, -1, 1, 0, 1, 0, -1, -1], [-1, -1, 0, 1, 1, 0, -2, -1], [-2, -2, 1, 1, 1, 1, -3, -1], [-3, -3, 1, 2, 2, 0, -4, -1], [-2, -2, 1, 1, 2, 0, -4, 0], [-1, -2, 0, 1, 2, 0, -3, 0], [-1, -1, 0, 1, 1, 0, -2, 0], [0, -1, 0, 1, 0, 0, -1, 0]]

@[expose] def r6LW : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 1, 0, 0], [-2, 1, 0, -1, 1, 1, 0, 0], [-3, 0, 0, 0, 1, 1, 0, 0], [-4, 1, -1, 0, 1, 2, 0, 0], [-3, 0, -1, 0, 1, 2, 0, 0], [-3, 0, 0, 0, 0, 2, 0, 0], [-2, 0, 0, 0, 0, 1, 1, -1], [-1, 0, 0, 0, 0, 0, 1, 0]]

theorem r6_a : wordMat Tag.E8 r6a = toMat Tag.E8.rank r6LA :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r6_ai : wordMat Tag.E8 r6a.reverse = toMat Tag.E8.rank r6LAi :=
  wordMat_reverse_eq r6_a (by decide +kernel)

theorem r6_b : wordMat Tag.E8 r6b = toMat Tag.E8.rank r6LB :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r6_bi : wordMat Tag.E8 r6b.reverse = toMat Tag.E8.rank r6LBi :=
  wordMat_reverse_eq r6_b (by decide +kernel)

theorem r6_c : wordMat Tag.E8 r6c = toMat Tag.E8.rank r6LC :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r6_ci : wordMat Tag.E8 r6c.reverse = toMat Tag.E8.rank r6LCi :=
  wordMat_reverse_eq r6_c (by decide +kernel)

theorem r6_d : wordMat Tag.E8 r6d = toMat Tag.E8.rank r6LD :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r6_di : wordMat Tag.E8 r6d.reverse = toMat Tag.E8.rank r6LDi :=
  wordMat_reverse_eq r6_d (by decide +kernel)

theorem r6_w : wordMat Tag.E8 e8SixWord = toMat Tag.E8.rank r6LW :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r6_dc :
    wordMat Tag.E8 (cw (cw r6a r6b) (cw r6c r6d)) =
      (-1 : ℤ) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) := by
  have h := dc_eq_smul_pow (w := ([] : List (Fin Tag.E8.rank))) r6_a r6_ai r6_b r6_bi r6_c r6_ci r6_d r6_di (W := lid Tag.E8.rank) (s := -1) (k := 0)
    (by rw [wordMat_nil, toMat_lid]) (by decide +kernel)
  rwa [pow_zero] at h

theorem r6_comm_a :
    wordMat Tag.E8 r6a * wordMat Tag.E8 e8SixWord = wordMat Tag.E8 e8SixWord * wordMat Tag.E8 r6a :=
  comm_of_lists r6_a r6_w (by decide +kernel)

theorem r6_comm_b :
    wordMat Tag.E8 r6b * wordMat Tag.E8 e8SixWord = wordMat Tag.E8 e8SixWord * wordMat Tag.E8 r6b :=
  comm_of_lists r6_b r6_w (by decide +kernel)

theorem r6_comm_c :
    wordMat Tag.E8 r6c * wordMat Tag.E8 e8SixWord = wordMat Tag.E8 e8SixWord * wordMat Tag.E8 r6c :=
  comm_of_lists r6_c r6_w (by decide +kernel)

theorem r6_comm_d :
    wordMat Tag.E8 r6d * wordMat Tag.E8 e8SixWord = wordMat Tag.E8 e8SixWord * wordMat Tag.E8 r6d :=
  comm_of_lists r6_d r6_w (by decide +kernel)

@[expose] def r8a : List (Fin Tag.E8.rank) :=
  [5, 6, 7, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 0]

@[expose] def r8b : List (Fin Tag.E8.rank) :=
  [7, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 2, 3, 2, 1]

@[expose] def r8c : List (Fin Tag.E8.rank) :=
  [4, 3, 2, 1, 3, 4, 5, 6, 7, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 3, 1]

@[expose] def r8d : List (Fin Tag.E8.rank) :=
  [5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2, 1, 3, 2, 1, 0]

@[expose] def r8LA : List (List ℤ) :=
  [[0, -1, -1, 2, -2, 2, -1, 0], [-1, -2, 0, 2, -2, 3, -2, 0], [0, -3, -1, 3, -3, 4, -2, 0], [-1, -4, -1, 4, -4, 6, -4, 1], [0, -3, -1, 3, -3, 5, -4, 1], [0, -2, -1, 2, -2, 4, -3, 0], [0, -1, -1, 1, -1, 3, -2, 0], [0, 0, 0, 0, -1, 2, -1, 0]]

@[expose] def r8LAi : List (List ℤ) :=
  [[0, 1, 1, -2, 2, -2, 1, 0], [1, 2, 0, -2, 2, -3, 2, 0], [0, 3, 1, -3, 3, -4, 2, 0], [1, 4, 1, -4, 4, -6, 4, -1], [0, 3, 1, -3, 3, -5, 4, -1], [0, 2, 1, -2, 2, -4, 3, 0], [0, 1, 1, -1, 1, -3, 2, 0], [0, 0, 0, 0, 1, -2, 1, 0]]

@[expose] def r8LB : List (List ℤ) :=
  [[1, -1, -1, 1, -1, 2, -1, 0], [0, -1, 0, 1, -2, 3, -1, 0], [1, -2, 0, 1, -2, 4, -2, 0], [1, -2, 0, 1, -3, 6, -3, 1], [1, -1, 0, 1, -3, 5, -3, 1], [0, -1, 0, 1, -2, 4, -3, 1], [0, 0, 0, 0, -1, 3, -2, 0], [0, 0, 0, 0, -1, 2, -1, 0]]

@[expose] def r8LBi : List (List ℤ) :=
  [[0, 0, 0, 0, 1, -1, 1, -2], [0, 1, -1, 0, 1, -1, 2, -3], [-1, 1, 0, 0, 1, -1, 2, -4], [0, 2, -1, 0, 1, -1, 3, -6], [0, 1, -1, 1, 0, -1, 3, -5], [0, 1, -1, 1, 0, -1, 2, -3], [0, 1, -1, 1, 0, -1, 1, -2], [0, 0, -1, 1, 0, 0, 0, -1]]

@[expose] def r8LC : List (List ℤ) :=
  [[0, 0, 0, 0, -1, 2, -1, 1], [0, 0, 1, 0, -2, 3, -2, 1], [1, 0, 0, 0, -2, 4, -3, 2], [1, 0, 1, 0, -4, 6, -4, 3], [1, -1, 1, 0, -3, 5, -3, 2], [1, -1, 1, 0, -2, 3, -2, 2], [1, -1, 0, 1, -2, 2, -1, 1], [0, -1, 0, 1, -1, 1, -1, 1]]

@[expose] def r8LCi : List (List ℤ) :=
  [[0, 1, 1, -1, -1, 1, 1, -1], [1, 2, 1, -1, -2, 1, 1, -1], [1, 3, 1, -2, -2, 2, 1, -1], [2, 4, 2, -3, -3, 2, 2, -1], [2, 3, 2, -3, -2, 2, 1, -1], [2, 2, 1, -2, -1, 1, 1, -1], [2, 1, 0, -1, -1, 1, 1, -1], [1, 0, 0, 0, -1, 1, 0, 0]]

@[expose] def r8LD : List (List ℤ) :=
  [[0, 0, 0, -1, 2, -1, -1, 2], [-1, -1, 1, -1, 2, -1, -1, 3], [-1, -1, 1, -1, 3, -2, -2, 4], [-2, -2, 1, -1, 4, -2, -3, 6], [-1, -2, 0, 0, 3, -2, -2, 5], [-1, -1, 0, 0, 2, -2, -1, 4], [-1, 0, 0, 0, 1, -1, -1, 3], [-1, 0, 0, 0, 1, -1, 0, 1]]

@[expose] def r8LDi : List (List ℤ) :=
  [[0, 1, 1, -2, 2, -2, 1, 0], [0, 1, 1, -2, 2, -3, 2, 1], [-1, 2, 2, -3, 3, -4, 2, 1], [-1, 2, 2, -4, 5, -6, 3, 2], [0, 2, 1, -3, 4, -5, 2, 2], [0, 2, 0, -2, 3, -4, 2, 1], [0, 2, 0, -2, 2, -2, 1, 1], [0, 1, 0, -1, 1, -1, 1, 0]]

@[expose] def r8LW : List (List ℤ) :=
  [[0, 2, 0, -1, 0, 0, 1, -1], [0, 2, 1, -2, 1, -1, 2, -2], [1, 3, 0, -2, 1, -1, 2, -2], [0, 4, 1, -3, 2, -2, 3, -3], [0, 3, 1, -2, 1, -2, 3, -2], [0, 2, 1, -1, 0, -1, 2, -2], [0, 2, 1, -1, 0, -1, 1, -1], [0, 1, 1, -1, 0, 0, 0, 0]]

theorem r8_a : wordMat Tag.E8 r8a = toMat Tag.E8.rank r8LA :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r8_ai : wordMat Tag.E8 r8a.reverse = toMat Tag.E8.rank r8LAi :=
  wordMat_reverse_eq r8_a (by decide +kernel)

theorem r8_b : wordMat Tag.E8 r8b = toMat Tag.E8.rank r8LB :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r8_bi : wordMat Tag.E8 r8b.reverse = toMat Tag.E8.rank r8LBi :=
  wordMat_reverse_eq r8_b (by decide +kernel)

theorem r8_c : wordMat Tag.E8 r8c = toMat Tag.E8.rank r8LC :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r8_ci : wordMat Tag.E8 r8c.reverse = toMat Tag.E8.rank r8LCi :=
  wordMat_reverse_eq r8_c (by decide +kernel)

theorem r8_d : wordMat Tag.E8 r8d = toMat Tag.E8.rank r8LD :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r8_di : wordMat Tag.E8 r8d.reverse = toMat Tag.E8.rank r8LDi :=
  wordMat_reverse_eq r8_d (by decide +kernel)

theorem r8_w : wordMat Tag.E8 e8EightWord = toMat Tag.E8.rank r8LW :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r8_dc :
    wordMat Tag.E8 (cw (cw r8a r8b) (cw r8c r8d)) =
      (-1 : ℤ) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) := by
  have h := dc_eq_smul_pow (w := ([] : List (Fin Tag.E8.rank))) r8_a r8_ai r8_b r8_bi r8_c r8_ci r8_d r8_di (W := lid Tag.E8.rank) (s := -1) (k := 0)
    (by rw [wordMat_nil, toMat_lid]) (by decide +kernel)
  rwa [pow_zero] at h

theorem r8_comm_a :
    wordMat Tag.E8 r8a * wordMat Tag.E8 e8EightWord = wordMat Tag.E8 e8EightWord * wordMat Tag.E8 r8a :=
  comm_of_lists r8_a r8_w (by decide +kernel)

theorem r8_comm_b :
    wordMat Tag.E8 r8b * wordMat Tag.E8 e8EightWord = wordMat Tag.E8 e8EightWord * wordMat Tag.E8 r8b :=
  comm_of_lists r8_b r8_w (by decide +kernel)

theorem r8_comm_c :
    wordMat Tag.E8 r8c * wordMat Tag.E8 e8EightWord = wordMat Tag.E8 e8EightWord * wordMat Tag.E8 r8c :=
  comm_of_lists r8_c r8_w (by decide +kernel)

theorem r8_comm_d :
    wordMat Tag.E8 r8d * wordMat Tag.E8 e8EightWord = wordMat Tag.E8 e8EightWord * wordMat Tag.E8 r8d :=
  comm_of_lists r8_d r8_w (by decide +kernel)

end E8Data

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
