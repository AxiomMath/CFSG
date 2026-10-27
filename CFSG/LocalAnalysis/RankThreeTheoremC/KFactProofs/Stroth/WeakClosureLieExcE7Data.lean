module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcMat
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Two
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Three
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Four
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Six

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


namespace E7Data

@[expose] def r3a : List (Fin Tag.E7.rank) :=
  [6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4]

@[expose] def r3b : List (Fin Tag.E7.rank) :=
  [3, 0, 2, 1, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 0, 2, 3, 2, 1]

@[expose] def r3c : List (Fin Tag.E7.rank) :=
  [6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 2, 3, 0]

@[expose] def r3d : List (Fin Tag.E7.rank) :=
  [6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 2, 1, 3, 4, 2, 3, 1]

@[expose] def r3LA : List (List ℤ) :=
  [[1, 0, 0, 0, -1, 1, -1], [1, 1, 0, 0, -1, 0, -1], [1, 0, 0, 1, -2, 1, -2], [2, 0, 0, 1, -2, 0, -2], [1, 0, 1, 0, -1, 0, -2], [1, 0, 0, 0, 0, 0, -2], [0, 0, 0, 0, 0, 0, -1]]

@[expose] def r3LAi : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 1, -2], [-1, 1, 1, -1, 0, 1, -2], [-1, 0, 1, -1, 1, 1, -3], [-2, 0, 2, -1, 0, 2, -4], [-1, 0, 1, -1, 0, 2, -3], [0, 0, 1, -1, 0, 1, -2], [0, 0, 0, 0, 0, 0, -1]]

@[expose] def r3LB : List (List ℤ) :=
  [[0, 0, 0, 0, -1, 1, 1], [1, -1, -1, 1, -1, 1, 1], [0, -1, 0, 1, -2, 2, 1], [1, -2, 0, 1, -2, 2, 2], [1, -1, 0, 0, -1, 2, 1], [0, -1, 0, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def r3LBi : List (List ℤ) :=
  [[-1, 0, 0, 0, 1, -1, 1], [-1, 0, 1, -1, 1, -1, 2], [-2, -1, 1, 0, 1, -1, 2], [-3, 0, 2, -1, 1, -1, 3], [-2, 0, 1, -1, 1, 0, 2], [-1, 0, 1, -1, 1, 0, 1], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def r3LC : List (List ℤ) :=
  [[0, 1, 0, 0, -1, 0, 0], [-1, 0, 1, 0, -1, 0, 0], [-1, 1, 1, 0, -2, 1, -1], [-1, 1, 2, -1, -2, 1, -1], [-1, 1, 1, -1, -1, 1, -1], [-1, 1, 1, -1, 0, 0, -1], [0, 0, 0, 0, 0, 0, -1]]

@[expose] def r3LCi : List (List ℤ) :=
  [[0, -1, 0, 1, -1, 0, 0], [0, -1, 1, 0, -1, 1, -1], [-1, -1, 1, 1, -2, 1, -1], [-1, -1, 2, 0, -2, 1, -1], [-1, -1, 1, 0, -1, 1, -1], [-1, -1, 1, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, -1]]

@[expose] def r3LD : List (List ℤ) :=
  [[1, 0, 0, 0, 0, -1, 0], [1, -1, 0, 1, -1, 0, -1], [1, -1, 1, 0, 0, -1, -1], [2, -2, 0, 1, 0, -1, -2], [2, -1, 0, 0, 0, 0, -2], [1, -1, 0, 0, 0, 0, -1], [0, 0, 0, 0, 0, 0, -1]]

@[expose] def r3LDi : List (List ℤ) :=
  [[0, 0, 0, 0, 1, -1, -1], [0, 0, 0, 0, 1, -2, 0], [-1, 0, 1, 0, 1, -2, -1], [-1, 0, 0, 1, 1, -3, -1], [-1, -1, 0, 1, 1, -2, -1], [-1, 0, 0, 0, 1, -1, -1], [0, 0, 0, 0, 0, 0, -1]]

@[expose] def r3LW : List (List ℤ) :=
  [[0, -1, -1, 1, 0, 0, 1], [1, -1, -1, 1, -1, 1, 1], [1, -1, -2, 2, -1, 0, 2], [1, -1, -2, 2, -2, 1, 3], [0, -1, -1, 2, -2, 1, 2], [0, -1, 0, 1, -1, 0, 2], [0, 0, 0, 0, 0, 0, 1]]

theorem r3_a : wordMat Tag.E7 r3a = toMat Tag.E7.rank r3LA :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r3_ai : wordMat Tag.E7 r3a.reverse = toMat Tag.E7.rank r3LAi :=
  wordMat_reverse_eq r3_a (by decide +kernel)

theorem r3_b : wordMat Tag.E7 r3b = toMat Tag.E7.rank r3LB :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r3_bi : wordMat Tag.E7 r3b.reverse = toMat Tag.E7.rank r3LBi :=
  wordMat_reverse_eq r3_b (by decide +kernel)

theorem r3_c : wordMat Tag.E7 r3c = toMat Tag.E7.rank r3LC :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r3_ci : wordMat Tag.E7 r3c.reverse = toMat Tag.E7.rank r3LCi :=
  wordMat_reverse_eq r3_c (by decide +kernel)

theorem r3_d : wordMat Tag.E7 r3d = toMat Tag.E7.rank r3LD :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r3_di : wordMat Tag.E7 r3d.reverse = toMat Tag.E7.rank r3LDi :=
  wordMat_reverse_eq r3_d (by decide +kernel)

theorem r3_w : wordMat Tag.E7 e7ThreeWord = toMat Tag.E7.rank r3LW :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r3_dc :
    wordMat Tag.E7 (cw (cw r3a r3b) (cw r3c r3d)) = (1 : ℤ) • wordMat Tag.E7 e7ThreeWord ^ 2 :=
  dc_eq_smul_pow r3_a r3_ai r3_b r3_bi r3_c r3_ci r3_d r3_di r3_w (by decide +kernel)

theorem r3_comm_a :
    wordMat Tag.E7 r3a * wordMat Tag.E7 e7ThreeWord = wordMat Tag.E7 e7ThreeWord * wordMat Tag.E7 r3a :=
  comm_of_lists r3_a r3_w (by decide +kernel)

theorem r3_comm_b :
    wordMat Tag.E7 r3b * wordMat Tag.E7 e7ThreeWord = wordMat Tag.E7 e7ThreeWord * wordMat Tag.E7 r3b :=
  comm_of_lists r3_b r3_w (by decide +kernel)

theorem r3_comm_c :
    wordMat Tag.E7 r3c * wordMat Tag.E7 e7ThreeWord = wordMat Tag.E7 e7ThreeWord * wordMat Tag.E7 r3c :=
  comm_of_lists r3_c r3_w (by decide +kernel)

theorem r3_comm_d :
    wordMat Tag.E7 r3d * wordMat Tag.E7 e7ThreeWord = wordMat Tag.E7 e7ThreeWord * wordMat Tag.E7 r3d :=
  comm_of_lists r3_d r3_w (by decide +kernel)

@[expose] def r4a : List (Fin Tag.E7.rank) :=
  [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 0, 2, 1, 3, 4, 0, 2, 1, 3, 2, 0]

@[expose] def r4b : List (Fin Tag.E7.rank) :=
  [4, 3, 2, 1, 3, 4, 2, 1]

@[expose] def r4c : List (Fin Tag.E7.rank) :=
  [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 1, 3, 4]

@[expose] def r4d : List (Fin Tag.E7.rank) :=
  [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 2, 1, 3]

@[expose] def r4LA : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 1, -2], [-1, 1, 0, 0, 0, 1, -2], [-1, 1, 1, -1, 0, 2, -3], [-2, 1, 1, -1, 1, 2, -4], [-1, 1, 0, -1, 1, 2, -3], [-1, 0, 0, 0, 0, 2, -2], [0, 0, 0, 0, 0, 1, -1]]

@[expose] def r4LAi : List (List ℤ) :=
  [[0, 0, 0, 0, 0, -1, 2], [-1, 1, 0, 0, 0, -1, 2], [-1, 0, 0, 1, -1, -1, 3], [-1, 1, -1, 1, -1, -1, 4], [-1, 0, -1, 1, 0, -1, 3], [-1, 0, 0, 0, 0, 0, 2], [-1, 0, 0, 0, 0, 0, 1]]

@[expose] def r4LB : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0, 0], [1, 0, -1, 1, -1, 1, 0], [1, -1, 0, 1, -1, 1, 0], [1, 0, 0, 1, -2, 2, 0], [1, 0, 0, 0, -1, 2, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def r4LBi : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0, 0], [1, 0, -1, 1, -1, 1, 0], [1, -1, 0, 1, -1, 1, 0], [1, 0, 0, 1, -2, 2, 0], [1, 0, 0, 0, -1, 2, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def r4LC : List (List ℤ) :=
  [[0, 0, 0, 0, 0, -1, 2], [0, 0, 0, 1, -1, -1, 2], [0, 0, 1, 0, -1, -1, 3], [0, 1, 1, 0, -1, -2, 4], [1, 1, 0, 0, -1, -1, 3], [1, 0, 0, 0, 0, -1, 2], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def r4LCi : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 1, 0], [-1, 0, -1, 1, 0, 0, 1], [-2, 0, 0, 1, -1, 1, 1], [-2, 1, -1, 1, -1, 1, 2], [-1, 0, -1, 1, -1, 1, 2], [-1, 0, 0, 0, 0, 0, 2], [0, 0, 0, 0, 0, 0, 1]]

@[expose] def r4LD : List (List ℤ) :=
  [[1, 0, 0, 0, 0, -1, 0], [1, 1, 0, -1, 1, -2, 1], [1, 1, 1, -1, 0, -2, 1], [1, 1, 1, -1, 1, -4, 2], [1, 0, 1, -1, 1, -3, 2], [1, 0, 0, 0, 0, -2, 2], [1, 0, 0, 0, 0, -1, 1]]

@[expose] def r4LDi : List (List ℤ) :=
  [[0, 0, 0, 0, 0, -1, 2], [-1, 0, 0, 1, -1, -1, 2], [-1, -1, 0, 1, 0, -2, 3], [-1, -1, -1, 2, -1, -2, 4], [-1, 0, -1, 1, 0, -2, 3], [-1, 0, 0, 0, 0, -1, 2], [-1, 0, 0, 0, 0, 0, 1]]

@[expose] def r4LW : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, -1, 1, 0], [1, 0, 1, -1, 0, 1, 0], [0, 0, 2, -1, 0, 1, 0], [0, 1, 1, -1, 0, 1, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]]

theorem r4_a : wordMat Tag.E7 r4a = toMat Tag.E7.rank r4LA :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r4_ai : wordMat Tag.E7 r4a.reverse = toMat Tag.E7.rank r4LAi :=
  wordMat_reverse_eq r4_a (by decide +kernel)

theorem r4_b : wordMat Tag.E7 r4b = toMat Tag.E7.rank r4LB :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r4_bi : wordMat Tag.E7 r4b.reverse = toMat Tag.E7.rank r4LBi :=
  wordMat_reverse_eq r4_b (by decide +kernel)

theorem r4_c : wordMat Tag.E7 r4c = toMat Tag.E7.rank r4LC :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r4_ci : wordMat Tag.E7 r4c.reverse = toMat Tag.E7.rank r4LCi :=
  wordMat_reverse_eq r4_c (by decide +kernel)

theorem r4_d : wordMat Tag.E7 r4d = toMat Tag.E7.rank r4LD :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r4_di : wordMat Tag.E7 r4d.reverse = toMat Tag.E7.rank r4LDi :=
  wordMat_reverse_eq r4_d (by decide +kernel)

theorem r4_w : wordMat Tag.E7 e7FourWord = toMat Tag.E7.rank r4LW :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r4_dc :
    wordMat Tag.E7 (cw (cw r4a r4b) (cw r4c r4d)) = (1 : ℤ) • wordMat Tag.E7 e7FourWord ^ 2 :=
  dc_eq_smul_pow r4_a r4_ai r4_b r4_bi r4_c r4_ci r4_d r4_di r4_w (by decide +kernel)

theorem r4_comm_a :
    wordMat Tag.E7 r4a * wordMat Tag.E7 e7FourWord = wordMat Tag.E7 e7FourWord * wordMat Tag.E7 r4a :=
  comm_of_lists r4_a r4_w (by decide +kernel)

theorem r4_comm_b :
    wordMat Tag.E7 r4b * wordMat Tag.E7 e7FourWord = wordMat Tag.E7 e7FourWord * wordMat Tag.E7 r4b :=
  comm_of_lists r4_b r4_w (by decide +kernel)

theorem r4_comm_c :
    wordMat Tag.E7 r4c * wordMat Tag.E7 e7FourWord = wordMat Tag.E7 e7FourWord * wordMat Tag.E7 r4c :=
  comm_of_lists r4_c r4_w (by decide +kernel)

theorem r4_comm_d :
    wordMat Tag.E7 r4d * wordMat Tag.E7 e7FourWord = wordMat Tag.E7 e7FourWord * wordMat Tag.E7 r4d :=
  comm_of_lists r4_d r4_w (by decide +kernel)

@[expose] def r6a : List (Fin Tag.E7.rank) :=
  [6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2, 1, 3, 4, 2, 0]

@[expose] def r6b : List (Fin Tag.E7.rank) :=
  [4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 0, 2, 3, 4, 3, 0, 2, 1, 3, 0, 2, 1, 0]

@[expose] def r6c : List (Fin Tag.E7.rank) :=
  [6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4, 0, 2, 0]

@[expose] def r6d : List (Fin Tag.E7.rank) :=
  [6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0, 2, 1, 3, 4, 2, 1, 3]

@[expose] def r6LA : List (List ℤ) :=
  [[0, 0, 0, 1, -2, 1, 0], [-1, 1, 0, 1, -2, 1, 0], [-1, 1, 1, 1, -3, 1, 0], [-2, 1, 1, 2, -4, 2, -1], [-2, 1, 1, 1, -3, 2, -1], [-1, 1, 1, 0, -2, 2, -1], [0, 1, 0, 0, -1, 1, -1]]

@[expose] def r6LAi : List (List ℤ) :=
  [[0, 0, 0, 1, -2, 1, 0], [-1, 1, 0, 1, -2, 1, 0], [-1, 0, 0, 2, -3, 2, -1], [-1, 1, -1, 3, -4, 2, -1], [-1, 1, -1, 2, -3, 2, -1], [0, 1, -1, 1, -2, 2, -1], [0, 1, 0, 0, -1, 1, -1]]

@[expose] def r6LB : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 0, 0], [-1, -1, 0, 0, 1, -1, 1], [-2, -1, 0, 0, 1, 0, 0], [-2, -1, -1, 0, 2, -1, 1], [-1, -1, -1, 0, 2, -1, 0], [-1, -1, -1, 1, 1, -1, 0], [-1, 0, 0, 0, 1, -1, 0]]

@[expose] def r6LBi : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 0, 0], [-1, -1, 0, 1, -1, 0, 1], [-2, 0, 1, 0, -1, 0, 1], [-3, -1, 1, 1, -2, 1, 1], [-3, -1, 1, 1, -1, 0, 1], [-2, -1, 1, 1, -1, 0, 0], [-1, 0, 0, 1, -1, 0, 0]]

@[expose] def r6LC : List (List ℤ) :=
  [[0, 0, 0, 1, -2, 1, 0], [-1, 1, 0, 1, -2, 1, 0], [0, 1, -1, 2, -3, 1, 0], [-1, 2, 0, 2, -4, 1, 0], [-1, 2, 0, 1, -3, 1, 0], [0, 2, 0, 0, -2, 1, 0], [0, 1, 0, 0, -1, 1, -1]]

@[expose] def r6LCi : List (List ℤ) :=
  [[0, 0, 0, 1, -2, 1, 0], [-1, 1, 0, 1, -2, 1, 0], [0, 1, -1, 2, -3, 1, 0], [-1, 2, 0, 2, -4, 1, 0], [-1, 2, 0, 1, -3, 1, 0], [0, 2, 0, 0, -2, 1, 0], [0, 1, 0, 0, -1, 1, -1]]

@[expose] def r6LD : List (List ℤ) :=
  [[1, 0, 0, 0, -1, 0, 1], [1, 1, 1, -1, -1, 0, 1], [1, 1, 1, -1, -1, -1, 2], [2, 1, 2, -2, -1, -1, 2], [1, 1, 2, -2, -1, 0, 1], [1, 1, 1, -2, 0, 0, 1], [1, 1, 0, -1, 0, 0, 0]]

@[expose] def r6LDi : List (List ℤ) :=
  [[0, 1, -1, 1, -1, 0, 0], [-1, 2, 0, 0, -1, 0, 0], [-1, 2, -1, 1, -1, 0, -1], [-1, 3, -1, 1, -2, 0, -1], [-1, 2, -1, 1, -2, 1, -1], [0, 2, -1, 0, -1, 1, -1], [0, 1, 0, 0, -1, 1, -1]]

@[expose] def r6LW : List (List ℤ) :=
  [[1, -1, 0, 0, 0, 0, 1], [1, -1, 0, 1, -1, 0, 1], [1, -1, 1, 0, -1, 0, 2], [1, -2, 1, 1, -2, 1, 2], [0, -2, 1, 1, -1, 0, 2], [0, -2, 1, 1, -1, 0, 1], [0, -1, 0, 1, -1, 0, 1]]

theorem r6_a : wordMat Tag.E7 r6a = toMat Tag.E7.rank r6LA :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r6_ai : wordMat Tag.E7 r6a.reverse = toMat Tag.E7.rank r6LAi :=
  wordMat_reverse_eq r6_a (by decide +kernel)

theorem r6_b : wordMat Tag.E7 r6b = toMat Tag.E7.rank r6LB :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r6_bi : wordMat Tag.E7 r6b.reverse = toMat Tag.E7.rank r6LBi :=
  wordMat_reverse_eq r6_b (by decide +kernel)

theorem r6_c : wordMat Tag.E7 r6c = toMat Tag.E7.rank r6LC :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r6_ci : wordMat Tag.E7 r6c.reverse = toMat Tag.E7.rank r6LCi :=
  wordMat_reverse_eq r6_c (by decide +kernel)

theorem r6_d : wordMat Tag.E7 r6d = toMat Tag.E7.rank r6LD :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r6_di : wordMat Tag.E7 r6d.reverse = toMat Tag.E7.rank r6LDi :=
  wordMat_reverse_eq r6_d (by decide +kernel)

theorem r6_w : wordMat Tag.E7 e7SixWord = toMat Tag.E7.rank r6LW :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r6_dc :
    wordMat Tag.E7 (cw (cw r6a r6b) (cw r6c r6d)) = (1 : ℤ) • wordMat Tag.E7 e7SixWord ^ 4 :=
  dc_eq_smul_pow r6_a r6_ai r6_b r6_bi r6_c r6_ci r6_d r6_di r6_w (by decide +kernel)

theorem r6_comm_a :
    wordMat Tag.E7 r6a * wordMat Tag.E7 e7SixWord = wordMat Tag.E7 e7SixWord * wordMat Tag.E7 r6a :=
  comm_of_lists r6_a r6_w (by decide +kernel)

theorem r6_comm_b :
    wordMat Tag.E7 r6b * wordMat Tag.E7 e7SixWord = wordMat Tag.E7 e7SixWord * wordMat Tag.E7 r6b :=
  comm_of_lists r6_b r6_w (by decide +kernel)

theorem r6_comm_c :
    wordMat Tag.E7 r6c * wordMat Tag.E7 e7SixWord = wordMat Tag.E7 e7SixWord * wordMat Tag.E7 r6c :=
  comm_of_lists r6_c r6_w (by decide +kernel)

theorem r6_comm_d :
    wordMat Tag.E7 r6d * wordMat Tag.E7 e7SixWord = wordMat Tag.E7 e7SixWord * wordMat Tag.E7 r6d :=
  comm_of_lists r6_d r6_w (by decide +kernel)

@[expose] def u1a : List (Fin Tag.E7.rank) :=
  [3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 0, 2, 1, 3, 4, 1, 3, 1]

@[expose] def u1b : List (Fin Tag.E7.rank) :=
  [0, 2, 3, 4, 5, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 0, 2, 1, 3, 4, 3, 0]

@[expose] def u1c : List (Fin Tag.E7.rank) :=
  [3, 4, 5, 6, 3, 2, 1, 3, 4, 5, 4, 3, 0, 2, 1, 3, 4, 0, 2, 1, 3, 2, 0]

@[expose] def u1d : List (Fin Tag.E7.rank) :=
  [3, 4, 5, 6, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1, 3, 2, 1, 0]

@[expose] def u1LA : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 1, -2], [0, 0, 1, 0, -1, 1, -2], [0, -1, 1, 0, 0, 1, -3], [0, 0, 2, -1, 0, 1, -4], [0, 0, 2, -1, 0, 1, -3], [1, 0, 1, -1, 0, 1, -2], [0, 0, 1, -1, 0, 1, -1]]

@[expose] def u1LAi : List (List ℤ) :=
  [[0, 0, 0, -1, 1, 1, -1], [1, 0, -1, -1, 2, 0, -1], [0, 0, 0, -2, 3, 0, -1], [1, 0, 0, -3, 4, 0, -2], [1, -1, 0, -2, 3, 0, -1], [1, 0, 0, -2, 2, 0, 0], [0, 0, 0, -1, 1, 0, 0]]

@[expose] def u1LB : List (List ℤ) :=
  [[-1, 1, 1, 0, -1, 0, 0], [-1, 1, 1, 0, -1, 0, 1], [-1, 1, 2, 0, -2, 0, 1], [-2, 2, 3, -1, -2, 0, 2], [-2, 1, 2, 0, -2, 0, 2], [-1, 1, 1, 0, -2, 1, 1], [0, 1, 0, 0, -1, 0, 1]]

@[expose] def u1LBi : List (List ℤ) :=
  [[-1, 1, 1, 0, -1, 0, 0], [0, 2, 0, 0, -1, 0, 0], [-1, 2, 1, 0, -1, 0, -1], [-1, 4, 1, -1, -1, 0, -1], [-1, 3, 0, 0, -1, 0, -1], [-1, 2, 0, 0, -1, 1, -1], [-1, 1, 0, 0, 0, 0, 0]]

@[expose] def u1LC : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 1, 0], [-1, 1, 0, -1, 1, 0, 1], [-2, 1, 1, -1, 0, 1, 1], [-3, 2, 1, -2, 1, 1, 1], [-2, 2, 0, -1, 0, 1, 1], [-1, 2, 0, -1, 0, 1, 0], [0, 1, 0, -1, 0, 1, 0]]

@[expose] def u1LCi : List (List ℤ) :=
  [[0, 1, 1, -1, -1, 1, 0], [0, 1, 1, -1, -1, 2, -1], [0, 1, 2, -1, -2, 2, -1], [1, 2, 2, -2, -2, 3, -2], [1, 2, 1, -1, -2, 2, -1], [1, 1, 1, -1, -1, 1, 0], [0, 1, 1, -1, 0, 0, 0]]

@[expose] def u1LD : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 1, 0], [-1, 0, 1, -1, 0, 1, 1], [-2, -1, 1, 0, 0, 1, 1], [-3, -1, 2, -1, 0, 2, 1], [-2, -1, 2, -1, 0, 2, 0], [-2, 0, 2, -1, 0, 1, 0], [-1, 0, 1, -1, 1, 0, 0]]

@[expose] def u1LDi : List (List ℤ) :=
  [[0, 1, 1, -2, 1, 0, 0], [1, 1, 1, -2, 0, 1, 0], [0, 1, 2, -3, 1, 1, 0], [1, 1, 3, -4, 1, 1, 0], [1, 1, 2, -3, 1, 0, 1], [1, 1, 1, -2, 1, 0, 0], [0, 1, 1, -1, 0, 0, 0]]

theorem u1_a : wordMat Tag.E7 u1a = toMat Tag.E7.rank u1LA :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem u1_ai : wordMat Tag.E7 u1a.reverse = toMat Tag.E7.rank u1LAi :=
  wordMat_reverse_eq u1_a (by decide +kernel)

theorem u1_b : wordMat Tag.E7 u1b = toMat Tag.E7.rank u1LB :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem u1_bi : wordMat Tag.E7 u1b.reverse = toMat Tag.E7.rank u1LBi :=
  wordMat_reverse_eq u1_b (by decide +kernel)

theorem u1_c : wordMat Tag.E7 u1c = toMat Tag.E7.rank u1LC :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem u1_ci : wordMat Tag.E7 u1c.reverse = toMat Tag.E7.rank u1LCi :=
  wordMat_reverse_eq u1_c (by decide +kernel)

theorem u1_d : wordMat Tag.E7 u1d = toMat Tag.E7.rank u1LD :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem u1_di : wordMat Tag.E7 u1d.reverse = toMat Tag.E7.rank u1LDi :=
  wordMat_reverse_eq u1_d (by decide +kernel)

@[expose] def u2a : List (Fin Tag.E7.rank) :=
  [2, 3, 4, 5, 6, 4, 3, 2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 0, 2, 1, 3, 1]

@[expose] def u2b : List (Fin Tag.E7.rank) :=
  [3, 0, 2, 1, 3, 4, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3, 0, 2, 1, 0]

@[expose] def u2c : List (Fin Tag.E7.rank) :=
  [1, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 0, 2, 1]

@[expose] def u2d : List (Fin Tag.E7.rank) :=
  [0, 2, 3, 4, 5, 6, 0, 2, 1, 3, 0, 2]

@[expose] def u2LA : List (List ℤ) :=
  [[0, 0, 1, -1, 0, 1, 0], [0, -1, 1, -1, 1, 0, 1], [0, -1, 2, -2, 1, 1, 0], [1, -2, 2, -2, 1, 1, 1], [1, -1, 2, -2, 1, 0, 1], [0, -1, 2, -1, 0, 0, 1], [0, -1, 1, 0, 0, 0, 0]]

@[expose] def u2LAi : List (List ℤ) :=
  [[1, 0, -1, 0, 1, -1, 1], [2, 1, -1, -1, 1, -1, 1], [2, 1, -1, -1, 1, -1, 2], [3, 2, -2, -1, 1, -2, 3], [2, 2, -1, -1, 1, -2, 2], [2, 1, -1, 0, 0, -1, 1], [1, 1, -1, 0, 0, 0, 0]]

@[expose] def u2LB : List (List ℤ) :=
  [[0, 0, -1, 0, 0, 1, 0], [0, 0, 0, -1, 0, 1, 1], [0, 0, -1, -1, 1, 1, 1], [0, -1, -1, -1, 1, 1, 2], [0, -1, -1, 0, 0, 1, 2], [0, 0, -1, 0, 0, 0, 2], [-1, 0, 0, 0, 0, 0, 1]]

@[expose] def u2LBi : List (List ℤ) :=
  [[-1, 0, 1, -1, 1, 0, -1], [-1, 0, 2, -2, 1, 0, 0], [-2, 0, 2, -2, 2, -1, 0], [-2, -1, 3, -3, 3, -1, 0], [-2, -1, 3, -2, 2, -1, 0], [-1, 0, 2, -2, 2, -1, 0], [-1, 0, 1, -1, 1, 0, 0]]

@[expose] def u2LC : List (List ℤ) :=
  [[0, 0, -1, 0, 1, -1, 1], [0, 0, -1, 0, 1, -1, 0], [0, 0, -2, 0, 2, -1, 0], [1, 0, -3, 0, 2, -1, 0], [1, -1, -2, 0, 2, -1, 0], [1, -1, -2, 1, 1, -1, 0], [0, -1, -1, 1, 0, 0, 0]]

@[expose] def u2LCi : List (List ℤ) :=
  [[0, -1, 0, 0, 0, 1, -1], [0, -1, 1, 0, -1, 1, -1], [0, -1, 1, -1, 0, 1, -1], [0, -2, 2, -1, -1, 2, -1], [0, -2, 2, -1, 0, 1, -1], [0, -2, 1, 0, 0, 0, 0], [1, -1, 0, 0, 0, 0, 0]]

@[expose] def u2LD : List (List ℤ) :=
  [[1, 0, -1, 0, 1, 0, -1], [1, 0, -1, 0, 1, 0, 0], [1, 1, -1, -1, 2, 0, -1], [1, 1, -2, 0, 2, 0, -1], [1, 1, -1, 0, 1, 0, -1], [0, 0, 0, 0, 1, 0, -1], [0, 0, 0, 0, 0, 1, -1]]

@[expose] def u2LDi : List (List ℤ) :=
  [[0, 1, 0, -1, 1, 0, 0], [-1, 0, 0, 0, 1, 0, 0], [-1, 1, 0, -1, 1, 1, 0], [-1, 1, -1, 0, 1, 1, 0], [-1, 1, 0, 0, 0, 1, 0], [-1, 1, 0, 0, 0, 0, 1], [-1, 1, 0, 0, 0, 0, 0]]

theorem u2_a : wordMat Tag.E7 u2a = toMat Tag.E7.rank u2LA :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem u2_ai : wordMat Tag.E7 u2a.reverse = toMat Tag.E7.rank u2LAi :=
  wordMat_reverse_eq u2_a (by decide +kernel)

theorem u2_b : wordMat Tag.E7 u2b = toMat Tag.E7.rank u2LB :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem u2_bi : wordMat Tag.E7 u2b.reverse = toMat Tag.E7.rank u2LBi :=
  wordMat_reverse_eq u2_b (by decide +kernel)

theorem u2_c : wordMat Tag.E7 u2c = toMat Tag.E7.rank u2LC :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem u2_ci : wordMat Tag.E7 u2c.reverse = toMat Tag.E7.rank u2LCi :=
  wordMat_reverse_eq u2_c (by decide +kernel)

theorem u2_d : wordMat Tag.E7 u2d = toMat Tag.E7.rank u2LD :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem u2_di : wordMat Tag.E7 u2d.reverse = toMat Tag.E7.rank u2LDi :=
  wordMat_reverse_eq u2_d (by decide +kernel)

@[expose] def uLY1 : List (List ℤ) :=
  [[0, -1, 0, 1, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0], [-1, -2, 0, 0, 2, -1, 1], [1, 2, -1, -1, 0, 0, 0], [2, 5, -2, -1, -2, 1, 0], [1, 2, -1, 0, -1, 0, 0], [0, 0, 0, 0, 0, 0, 0]]

@[expose] def uLY2 : List (List ℤ) :=
  [[1, 3, -1, 0, -2, 1, -1], [0, 0, 0, 0, 0, 0, 0], [3, 5, -2, 0, -4, 2, -2], [0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0]]

theorem pair_cert :
    (wordMat Tag.E7 (cw (cw u1a u1b) (cw u1c u1d)).reverse - 1) * toMat Tag.E7.rank uLY1 +
      (wordMat Tag.E7 (cw (cw u2a u2b) (cw u2c u2d)).reverse - 1) * toMat Tag.E7.rank uLY2 = 1 := by
  rw [wordMat_dc_inv_eq u1_a u1_ai u1_b u1_bi u1_c u1_ci u1_d u1_di, wordMat_dc_inv_eq u2_a u2_ai u2_b u2_bi u2_c u2_ci u2_d u2_di]
  exact cert2_of_lists (by decide +kernel)

theorem wordMat_e7TwoWord :
    wordMat Tag.E7 e7TwoWord = (-1 : ℤ) • (1 : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) ℤ) := by
  have h : wordMat Tag.E7 e7TwoWord =
      toMat Tag.E7.rank (lsmul Tag.E7.rank (-1) (lid Tag.E7.rank)) :=
    wordMat_eq_toMat _ _ (by decide +kernel)
  rw [h, toMat_lsmul, toMat_lid]

end E7Data

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
