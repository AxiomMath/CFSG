module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcMat
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Two
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Three
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Four
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Six

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration

set_option linter.unusedSectionVars false


namespace E6Data

@[expose] def r3a : List (Fin Tag.E6.rank) :=
  [5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 0, 2, 0]

@[expose] def r3b : List (Fin Tag.E6.rank) :=
  [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 4, 1, 3, 2]

@[expose] def r3c : List (Fin Tag.E6.rank) :=
  [5, 4, 3, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4, 1, 3, 0, 2, 0]

@[expose] def r3d : List (Fin Tag.E6.rank) :=
  [1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 1, 0]

@[expose] def r3LA : List (List ℤ) :=
  [[-1, 0, 0, 0, 1, -1], [0, 0, 0, -1, 2, -1], [0, 0, -1, 0, 2, -2], [0, 0, 0, -1, 3, -3], [0, 1, 0, -1, 2, -2], [0, 1, 0, -1, 1, -1]]

@[expose] def r3LAi : List (List ℤ) :=
  [[-1, 0, 0, 0, 1, -1], [0, 0, 0, -1, 2, -1], [0, 0, -1, 0, 2, -2], [0, 0, 0, -1, 3, -3], [0, 1, 0, -1, 2, -2], [0, 1, 0, -1, 1, -1]]

@[expose] def r3LB : List (List ℤ) :=
  [[0, 0, 0, 0, 0, -1], [1, 1, -1, 0, 0, -1], [1, 0, -1, 1, -1, -1], [2, 0, -2, 1, 0, -2], [1, 0, -1, 1, 0, -2], [1, 0, 0, 0, 0, -1]]

@[expose] def r3LBi : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 1], [-1, 1, 0, -1, 1, 0], [-1, 0, 0, -1, 1, 1], [-2, 0, 0, -1, 2, 0], [-1, 0, -1, 0, 1, 0], [-1, 0, 0, 0, 0, 0]]

@[expose] def r3LC : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 1], [-1, 1, 0, 0, -1, 1], [-2, 0, 0, 1, -1, 1], [-2, 1, -1, 1, -1, 1], [-2, 1, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0]]

@[expose] def r3LCi : List (List ℤ) :=
  [[0, 0, 0, 0, 0, -1], [0, 0, 0, 0, 1, -2], [0, 0, 1, -1, 1, -2], [0, -1, 1, 0, 1, -3], [1, -1, 0, 0, 1, -2], [1, 0, 0, 0, 0, -1]]

@[expose] def r3LD : List (List ℤ) :=
  [[0, -1, 0, 1, 0, -1], [0, 0, 0, 0, 1, -2], [0, 0, 0, 1, 0, -2], [-1, 0, 0, 1, 1, -3], [-1, 0, 1, 0, 1, -2], [0, 0, 0, 0, 1, -1]]

@[expose] def r3LDi : List (List ℤ) :=
  [[0, 0, 1, -1, 0, 1], [-1, -1, 1, 0, 0, 1], [0, -1, 1, -1, 1, 1], [0, -2, 1, 0, 0, 2], [0, -1, 0, 0, 0, 2], [0, -1, 0, 0, 0, 1]]

@[expose] def r3LW : List (List ℤ) :=
  [[0, 0, 0, 0, 0, -1], [1, -1, -1, 1, 0, -1], [1, 0, -1, 1, -1, -1], [2, -1, -1, 1, -1, -1], [1, -1, 0, 1, -1, -1], [1, 0, 0, 0, 0, -1]]

theorem r3_a : wordMat Tag.E6 r3a = toMat Tag.E6.rank r3LA :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r3_ai : wordMat Tag.E6 r3a.reverse = toMat Tag.E6.rank r3LAi :=
  wordMat_reverse_eq r3_a (by decide +kernel)

theorem r3_b : wordMat Tag.E6 r3b = toMat Tag.E6.rank r3LB :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r3_bi : wordMat Tag.E6 r3b.reverse = toMat Tag.E6.rank r3LBi :=
  wordMat_reverse_eq r3_b (by decide +kernel)

theorem r3_c : wordMat Tag.E6 r3c = toMat Tag.E6.rank r3LC :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r3_ci : wordMat Tag.E6 r3c.reverse = toMat Tag.E6.rank r3LCi :=
  wordMat_reverse_eq r3_c (by decide +kernel)

theorem r3_d : wordMat Tag.E6 r3d = toMat Tag.E6.rank r3LD :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r3_di : wordMat Tag.E6 r3d.reverse = toMat Tag.E6.rank r3LDi :=
  wordMat_reverse_eq r3_d (by decide +kernel)

theorem r3_w : wordMat Tag.E6 e6ThreeWord = toMat Tag.E6.rank r3LW :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r3_dc :
    wordMat Tag.E6 (cw (cw r3a r3b) (cw r3c r3d)) = (1 : ℤ) • wordMat Tag.E6 e6ThreeWord ^ 2 :=
  dc_eq_smul_pow r3_a r3_ai r3_b r3_bi r3_c r3_ci r3_d r3_di r3_w (by decide +kernel)

theorem r3_comm_a :
    wordMat Tag.E6 r3a * wordMat Tag.E6 e6ThreeWord = wordMat Tag.E6 e6ThreeWord * wordMat Tag.E6 r3a :=
  comm_of_lists r3_a r3_w (by decide +kernel)

theorem r3_comm_b :
    wordMat Tag.E6 r3b * wordMat Tag.E6 e6ThreeWord = wordMat Tag.E6 e6ThreeWord * wordMat Tag.E6 r3b :=
  comm_of_lists r3_b r3_w (by decide +kernel)

theorem r3_comm_c :
    wordMat Tag.E6 r3c * wordMat Tag.E6 e6ThreeWord = wordMat Tag.E6 e6ThreeWord * wordMat Tag.E6 r3c :=
  comm_of_lists r3_c r3_w (by decide +kernel)

theorem r3_comm_d :
    wordMat Tag.E6 r3d * wordMat Tag.E6 e6ThreeWord = wordMat Tag.E6 e6ThreeWord * wordMat Tag.E6 r3d :=
  comm_of_lists r3_d r3_w (by decide +kernel)

@[expose] def r4a : List (Fin Tag.E6.rank) :=
  [5, 4, 3, 2, 1, 3, 4, 5, 4, 3, 0, 2, 1, 3, 4, 1, 3, 0, 2, 0]

@[expose] def r4b : List (Fin Tag.E6.rank) :=
  [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 1, 3, 4, 3, 2, 1, 3]

@[expose] def r4c : List (Fin Tag.E6.rank) :=
  [5, 4, 3, 2, 1, 3, 4, 5, 3, 4, 3, 2, 1]

@[expose] def r4d : List (Fin Tag.E6.rank) :=
  [5, 4, 3, 2, 1, 3, 4, 5, 2, 3, 4, 3, 2, 1, 3, 2, 1]

@[expose] def r4LA : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 1], [-1, 0, -1, 1, 0, 0], [-2, 0, 0, 1, -1, 1], [-2, 1, -1, 1, -1, 1], [-1, 0, -1, 1, -1, 1], [-1, 0, 0, 0, 0, 0]]

@[expose] def r4LAi : List (List ℤ) :=
  [[0, 0, 0, 0, 0, -1], [0, 0, 0, 1, -1, -1], [0, 0, 1, 0, -1, -1], [0, 1, 1, 0, -1, -2], [1, 1, 0, 0, -1, -1], [1, 0, 0, 0, 0, -1]]

@[expose] def r4LB : List (List ℤ) :=
  [[0, 0, 0, 0, 0, -1], [1, 0, 0, -1, 1, -1], [1, 1, 0, -1, 0, -1], [1, 1, 1, -2, 1, -2], [1, 0, 1, -1, 0, -1], [1, 0, 0, 0, 0, -1]]

@[expose] def r4LBi : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 1], [-1, -1, 0, 1, -1, 1], [-1, -1, -1, 1, 0, 1], [-1, -1, -1, 1, -1, 2], [-1, 0, -1, 1, -1, 1], [-1, 0, 0, 0, 0, 0]]

@[expose] def r4LC : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0], [1, 0, -1, 1, 0, -1], [1, -1, 0, 1, 0, -1], [2, -1, -1, 2, -1, -1], [2, -1, -1, 1, 0, -1], [1, 0, 0, 0, 0, -1]]

@[expose] def r4LCi : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0], [1, 1, 0, 0, -1, 0], [1, 0, 1, 0, -1, 0], [1, 1, 1, 0, -1, -1], [1, 1, 1, -1, 0, -1], [1, 0, 0, 0, 0, -1]]

@[expose] def r4LD : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0], [2, 0, -1, 0, 0, 0], [2, 0, -1, 0, 1, -1], [3, -1, -1, 0, 1, -1], [2, 0, 0, -1, 1, -1], [1, 0, 0, 0, 0, -1]]

@[expose] def r4LDi : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0], [1, 0, 1, -1, 0, 0], [2, -1, 0, 0, 0, 0], [2, -1, 1, 0, -1, 0], [1, -1, 1, 0, 0, -1], [1, 0, 0, 0, 0, -1]]

@[expose] def r4LW : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0], [1, 0, -1, 0, 1, 0], [1, 0, -1, 1, 0, 0], [2, 0, -2, 1, 0, 1], [1, -1, -1, 1, 0, 1], [0, 0, 0, 0, 0, 1]]

theorem r4_a : wordMat Tag.E6 r4a = toMat Tag.E6.rank r4LA :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r4_ai : wordMat Tag.E6 r4a.reverse = toMat Tag.E6.rank r4LAi :=
  wordMat_reverse_eq r4_a (by decide +kernel)

theorem r4_b : wordMat Tag.E6 r4b = toMat Tag.E6.rank r4LB :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r4_bi : wordMat Tag.E6 r4b.reverse = toMat Tag.E6.rank r4LBi :=
  wordMat_reverse_eq r4_b (by decide +kernel)

theorem r4_c : wordMat Tag.E6 r4c = toMat Tag.E6.rank r4LC :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r4_ci : wordMat Tag.E6 r4c.reverse = toMat Tag.E6.rank r4LCi :=
  wordMat_reverse_eq r4_c (by decide +kernel)

theorem r4_d : wordMat Tag.E6 r4d = toMat Tag.E6.rank r4LD :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r4_di : wordMat Tag.E6 r4d.reverse = toMat Tag.E6.rank r4LDi :=
  wordMat_reverse_eq r4_d (by decide +kernel)

theorem r4_w : wordMat Tag.E6 e6FourWord = toMat Tag.E6.rank r4LW :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r4_dc :
    wordMat Tag.E6 (cw (cw r4a r4b) (cw r4c r4d)) = (1 : ℤ) • wordMat Tag.E6 e6FourWord ^ 2 :=
  dc_eq_smul_pow r4_a r4_ai r4_b r4_bi r4_c r4_ci r4_d r4_di r4_w (by decide +kernel)

theorem r4_comm_a :
    wordMat Tag.E6 r4a * wordMat Tag.E6 e6FourWord = wordMat Tag.E6 e6FourWord * wordMat Tag.E6 r4a :=
  comm_of_lists r4_a r4_w (by decide +kernel)

theorem r4_comm_b :
    wordMat Tag.E6 r4b * wordMat Tag.E6 e6FourWord = wordMat Tag.E6 e6FourWord * wordMat Tag.E6 r4b :=
  comm_of_lists r4_b r4_w (by decide +kernel)

theorem r4_comm_c :
    wordMat Tag.E6 r4c * wordMat Tag.E6 e6FourWord = wordMat Tag.E6 e6FourWord * wordMat Tag.E6 r4c :=
  comm_of_lists r4_c r4_w (by decide +kernel)

theorem r4_comm_d :
    wordMat Tag.E6 r4d * wordMat Tag.E6 e6FourWord = wordMat Tag.E6 e6FourWord * wordMat Tag.E6 r4d :=
  comm_of_lists r4_d r4_w (by decide +kernel)

@[expose] def r6a : List (Fin Tag.E6.rank) :=
  [4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3, 2]

@[expose] def r6b : List (Fin Tag.E6.rank) :=
  [5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 2]

@[expose] def r6c : List (Fin Tag.E6.rank) :=
  [1, 3, 4, 5, 3, 0, 2, 1, 3, 4, 2, 1, 3, 2]

@[expose] def r6d : List (Fin Tag.E6.rank) :=
  [4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 2, 3]

@[expose] def r6LA : List (List ℤ) :=
  [[0, 0, 0, -1, 1, 0], [1, 0, 0, -1, 1, -1], [1, 0, -1, -1, 2, -1], [2, 1, -1, -2, 2, -1], [1, 1, -1, -1, 1, -1], [0, 1, 0, -1, 1, -1]]

@[expose] def r6LAi : List (List ℤ) :=
  [[-1, 0, 0, 1, -1, 0], [-1, -1, 0, 1, -1, 1], [-1, 0, 0, 1, -2, 1], [-2, -1, 1, 1, -2, 1], [-1, -1, 1, 1, -2, 1], [0, -1, 0, 1, -1, 0]]

@[expose] def r6LB : List (List ℤ) :=
  [[0, 0, 0, -1, 1, 0], [1, 0, 0, -1, 1, -1], [1, 0, -1, -1, 2, -1], [1, 0, 0, -2, 3, -2], [1, 1, 0, -2, 2, -1], [0, 1, 0, -1, 1, -1]]

@[expose] def r6LBi : List (List ℤ) :=
  [[-1, 0, 0, 0, 1, -1], [-1, -1, 0, 0, 1, 0], [-1, -1, -1, 1, 1, -1], [-2, -2, 0, 1, 1, -1], [-1, -2, 0, 1, 1, -1], [0, -1, 0, 0, 1, -1]]

@[expose] def r6LC : List (List ℤ) :=
  [[1, 0, -1, 0, 0, 1], [2, 0, -1, 0, 0, 0], [2, 0, -1, 0, 0, 1], [3, 1, -1, -1, 0, 1], [2, 1, -1, 0, -1, 1], [1, 1, -1, 0, 0, 0]]

@[expose] def r6LCi : List (List ℤ) :=
  [[-1, 0, 1, 0, 0, 0], [-1, -1, 1, 0, 0, 1], [-2, -1, 2, 0, 0, 0], [-2, -1, 3, -1, 0, 1], [-1, -1, 2, 0, -1, 1], [0, -1, 1, 0, 0, 0]]

@[expose] def r6LD : List (List ℤ) :=
  [[0, 1, 0, 0, -1, 1], [0, 0, 0, 0, -1, 2], [0, 1, 1, -1, -1, 2], [1, 1, 0, -1, -1, 3], [1, 1, 0, -1, -1, 2], [1, 0, 0, 0, -1, 1]]

@[expose] def r6LDi : List (List ℤ) :=
  [[0, -1, 0, 1, -1, 1], [1, -1, 0, 1, -1, 0], [0, -1, 1, 1, -2, 1], [1, -1, 0, 2, -3, 1], [0, -1, 0, 2, -2, 0], [0, 0, 0, 1, -1, 0]]

@[expose] def r6LW : List (List ℤ) :=
  [[-1, 0, 1, 0, 0, 0], [-1, -1, 1, 0, 0, 1], [-2, -1, 2, 0, 0, 0], [-2, -2, 2, 1, -1, 1], [-1, -2, 1, 1, 0, 0], [0, -1, 1, 0, 0, 0]]

theorem r6_a : wordMat Tag.E6 r6a = toMat Tag.E6.rank r6LA :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r6_ai : wordMat Tag.E6 r6a.reverse = toMat Tag.E6.rank r6LAi :=
  wordMat_reverse_eq r6_a (by decide +kernel)

theorem r6_b : wordMat Tag.E6 r6b = toMat Tag.E6.rank r6LB :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r6_bi : wordMat Tag.E6 r6b.reverse = toMat Tag.E6.rank r6LBi :=
  wordMat_reverse_eq r6_b (by decide +kernel)

theorem r6_c : wordMat Tag.E6 r6c = toMat Tag.E6.rank r6LC :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r6_ci : wordMat Tag.E6 r6c.reverse = toMat Tag.E6.rank r6LCi :=
  wordMat_reverse_eq r6_c (by decide +kernel)

theorem r6_d : wordMat Tag.E6 r6d = toMat Tag.E6.rank r6LD :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r6_di : wordMat Tag.E6 r6d.reverse = toMat Tag.E6.rank r6LDi :=
  wordMat_reverse_eq r6_d (by decide +kernel)

theorem r6_w : wordMat Tag.E6 e6SixWord = toMat Tag.E6.rank r6LW :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r6_dc :
    wordMat Tag.E6 (cw (cw r6a r6b) (cw r6c r6d)) = (1 : ℤ) • wordMat Tag.E6 e6SixWord ^ 3 :=
  dc_eq_smul_pow r6_a r6_ai r6_b r6_bi r6_c r6_ci r6_d r6_di r6_w (by decide +kernel)

theorem r6_comm_a :
    wordMat Tag.E6 r6a * wordMat Tag.E6 e6SixWord = wordMat Tag.E6 e6SixWord * wordMat Tag.E6 r6a :=
  comm_of_lists r6_a r6_w (by decide +kernel)

theorem r6_comm_b :
    wordMat Tag.E6 r6b * wordMat Tag.E6 e6SixWord = wordMat Tag.E6 e6SixWord * wordMat Tag.E6 r6b :=
  comm_of_lists r6_b r6_w (by decide +kernel)

theorem r6_comm_c :
    wordMat Tag.E6 r6c * wordMat Tag.E6 e6SixWord = wordMat Tag.E6 e6SixWord * wordMat Tag.E6 r6c :=
  comm_of_lists r6_c r6_w (by decide +kernel)

theorem r6_comm_d :
    wordMat Tag.E6 r6d * wordMat Tag.E6 e6SixWord = wordMat Tag.E6 e6SixWord * wordMat Tag.E6 r6d :=
  comm_of_lists r6_d r6_w (by decide +kernel)

@[expose] def r2a : List (Fin Tag.E6.rank) :=
  [0, 2, 1, 3, 4, 2, 1, 3, 0, 2, 0]

@[expose] def r2b : List (Fin Tag.E6.rank) :=
  [1, 3, 4, 2, 3, 1]

@[expose] def r2c : List (Fin Tag.E6.rank) :=
  [0, 2, 3, 4, 2, 3, 0, 2, 1, 3, 0, 2, 0]

@[expose] def r2d : List (Fin Tag.E6.rank) :=
  [5, 4, 3, 2, 1, 3, 4, 5, 4, 3]

@[expose] def r2LA : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 1], [0, 1, -1, 0, 0, 1], [-1, 0, -1, 1, 0, 1], [-1, 1, -1, 0, 1, 1], [-1, 1, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1]]

@[expose] def r2LAi : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 1], [-1, 0, 0, 0, 1, 0], [-1, -1, 0, 0, 1, 1], [-2, -1, 1, 0, 1, 1], [-1, -1, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1]]

@[expose] def r2LB : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0], [1, -1, 0, 0, 0, 1], [1, -1, 0, 0, 1, 0], [1, -2, 0, 1, 0, 1], [0, -1, 1, 0, 0, 1], [0, 0, 0, 0, 0, 1]]

@[expose] def r2LBi : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0], [1, -1, 0, 0, 0, 1], [1, -1, 0, 0, 1, 0], [1, -2, 0, 1, 0, 1], [0, -1, 1, 0, 0, 1], [0, 0, 0, 0, 0, 1]]

@[expose] def r2LC : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 1], [-1, 0, 0, 0, 1, 0], [-1, 1, 0, -1, 1, 1], [-1, 0, 0, -1, 2, 1], [0, 0, -1, 0, 1, 1], [0, 0, 0, 0, 0, 1]]

@[expose] def r2LCi : List (List ℤ) :=
  [[-1, 0, 0, 0, 0, 1], [-1, 1, 1, -1, 0, 1], [-1, 1, 0, 0, -1, 2], [-1, 2, 0, -1, 0, 2], [-1, 1, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1]]

@[expose] def r2LD : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, -1], [1, 1, 0, 0, 0, -1], [1, 1, 1, -1, 1, -2], [1, 1, 1, -1, 0, -1], [1, 0, 0, 0, 0, -1]]

@[expose] def r2LDi : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, -1], [1, 1, 0, 0, 0, -1], [1, 1, 1, 0, -1, -1], [1, 0, 0, 1, -1, -1], [1, 0, 0, 0, 0, -1]]

@[expose] def r2LW : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0], [1, -1, 0, 0, 0, 1], [2, 0, -1, 0, 0, 1], [2, 0, 0, -1, 0, 2], [1, 0, 0, 0, -1, 2], [0, 0, 0, 0, 0, 1]]

theorem r2_a : wordMat Tag.E6 r2a = toMat Tag.E6.rank r2LA :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r2_ai : wordMat Tag.E6 r2a.reverse = toMat Tag.E6.rank r2LAi :=
  wordMat_reverse_eq r2_a (by decide +kernel)

theorem r2_b : wordMat Tag.E6 r2b = toMat Tag.E6.rank r2LB :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r2_bi : wordMat Tag.E6 r2b.reverse = toMat Tag.E6.rank r2LBi :=
  wordMat_reverse_eq r2_b (by decide +kernel)

theorem r2_c : wordMat Tag.E6 r2c = toMat Tag.E6.rank r2LC :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r2_ci : wordMat Tag.E6 r2c.reverse = toMat Tag.E6.rank r2LCi :=
  wordMat_reverse_eq r2_c (by decide +kernel)

theorem r2_d : wordMat Tag.E6 r2d = toMat Tag.E6.rank r2LD :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r2_di : wordMat Tag.E6 r2d.reverse = toMat Tag.E6.rank r2LDi :=
  wordMat_reverse_eq r2_d (by decide +kernel)

theorem r2_w : wordMat Tag.E6 e6TwoWord = toMat Tag.E6.rank r2LW :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r2_dc :
    wordMat Tag.E6 (cw (cw r2a r2b) (cw r2c r2d)) = (1 : ℤ) • wordMat Tag.E6 e6TwoWord ^ 1 :=
  dc_eq_smul_pow r2_a r2_ai r2_b r2_bi r2_c r2_ci r2_d r2_di r2_w (by decide +kernel)

theorem r2_comm_a :
    wordMat Tag.E6 r2a * wordMat Tag.E6 e6TwoWord = wordMat Tag.E6 e6TwoWord * wordMat Tag.E6 r2a :=
  comm_of_lists r2_a r2_w (by decide +kernel)

theorem r2_comm_b :
    wordMat Tag.E6 r2b * wordMat Tag.E6 e6TwoWord = wordMat Tag.E6 e6TwoWord * wordMat Tag.E6 r2b :=
  comm_of_lists r2_b r2_w (by decide +kernel)

theorem r2_comm_c :
    wordMat Tag.E6 r2c * wordMat Tag.E6 e6TwoWord = wordMat Tag.E6 e6TwoWord * wordMat Tag.E6 r2c :=
  comm_of_lists r2_c r2_w (by decide +kernel)

theorem r2_comm_d :
    wordMat Tag.E6 r2d * wordMat Tag.E6 e6TwoWord = wordMat Tag.E6 e6TwoWord * wordMat Tag.E6 r2d :=
  comm_of_lists r2_d r2_w (by decide +kernel)

@[expose] def r1a : List (Fin Tag.E6.rank) :=
  [4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 2, 1, 3, 4, 3, 2, 1, 3, 1, 0]

@[expose] def r1b : List (Fin Tag.E6.rank) :=
  [5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 1, 3, 0, 2, 1, 0]

@[expose] def r1c : List (Fin Tag.E6.rank) :=
  [4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 4, 3, 0, 2, 1, 3, 2, 1, 0]

@[expose] def r1d : List (Fin Tag.E6.rank) :=
  [0, 2, 3, 4, 5, 1, 3, 4, 0, 2, 1, 3, 2]

@[expose] def r1LA : List (List ℤ) :=
  [[-1, -1, 1, 0, 0, 0], [-1, 0, 2, -1, 0, 0], [-2, 0, 2, -1, 0, 0], [-3, 0, 3, -1, 0, 0], [-2, 0, 2, -1, 1, -1], [-1, 0, 1, -1, 1, 0]]

@[expose] def r1LAi : List (List ℤ) :=
  [[0, 1, -1, 0, 0, 0], [-1, 0, -1, 1, 0, 0], [0, 1, -2, 1, 0, 0], [0, 0, -3, 2, 0, 0], [0, 0, -2, 1, 0, 1], [0, 0, -1, 1, -1, 1]]

@[expose] def r1LB : List (List ℤ) :=
  [[-1, 0, 0, 1, -1, 0], [-1, 0, -1, 1, 0, 0], [-2, 0, 0, 1, 0, -1], [-3, 0, 0, 1, 0, 0], [-2, -1, 0, 1, 0, 0], [-1, 0, 0, 0, 0, 0]]

@[expose] def r1LBi : List (List ℤ) :=
  [[0, 0, 0, 0, 0, -1], [0, 0, 0, 1, -1, -1], [0, -1, 0, 1, 0, -2], [0, 0, 0, 1, 0, -3], [-1, 0, 0, 1, 0, -2], [0, 0, -1, 1, 0, -1]]

@[expose] def r1LC : List (List ℤ) :=
  [[-1, 0, 0, 0, 1, -1], [-1, -1, 0, 0, 1, 0], [-2, -1, 1, 0, 1, -1], [-2, -2, 1, 0, 2, -1], [-1, -1, 1, -1, 2, -1], [-1, 0, 1, -1, 1, 0]]

@[expose] def r1LCi : List (List ℤ) :=
  [[0, -1, -1, 1, 0, 0], [1, -1, -1, 1, -1, 1], [0, -2, -1, 2, -1, 1], [1, -2, -2, 3, -2, 1], [1, -1, -2, 2, -1, 1], [0, 0, -1, 1, -1, 1]]

@[expose] def r1LD : List (List ℤ) :=
  [[1, 1, 0, -1, 0, 0], [1, 1, 0, -1, 0, 1], [1, 2, 0, -2, 1, 0], [2, 2, 0, -2, 1, 0], [2, 1, -1, -1, 1, 0], [1, 1, -1, 0, 0, 0]]

@[expose] def r1LDi : List (List ℤ) :=
  [[0, 0, -1, 1, 0, 0], [-1, 0, 0, 1, -1, 1], [-1, 0, -1, 2, -1, 0], [-2, 0, -1, 2, -1, 1], [-2, 0, 0, 1, 0, 0], [-1, 1, 0, 0, 0, 0]]

theorem r1_a : wordMat Tag.E6 r1a = toMat Tag.E6.rank r1LA :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r1_ai : wordMat Tag.E6 r1a.reverse = toMat Tag.E6.rank r1LAi :=
  wordMat_reverse_eq r1_a (by decide +kernel)

theorem r1_b : wordMat Tag.E6 r1b = toMat Tag.E6.rank r1LB :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r1_bi : wordMat Tag.E6 r1b.reverse = toMat Tag.E6.rank r1LBi :=
  wordMat_reverse_eq r1_b (by decide +kernel)

theorem r1_c : wordMat Tag.E6 r1c = toMat Tag.E6.rank r1LC :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r1_ci : wordMat Tag.E6 r1c.reverse = toMat Tag.E6.rank r1LCi :=
  wordMat_reverse_eq r1_c (by decide +kernel)

theorem r1_d : wordMat Tag.E6 r1d = toMat Tag.E6.rank r1LD :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r1_di : wordMat Tag.E6 r1d.reverse = toMat Tag.E6.rank r1LDi :=
  wordMat_reverse_eq r1_d (by decide +kernel)

@[expose] def r1LY : List (List ℤ) :=
  [[-2, 3, -1, -1, 2, -2], [-3, 0, 0, 0, 0, 0], [-1, 3, -2, -2, 4, -4], [-3, 3, 0, -3, 3, -3], [-2, 3, -1, -1, -1, 1], [-1, 0, 1, 1, -2, -1]]

theorem r1_cert :
    (wordMat Tag.E6 (cw (cw r1a r1b) (cw r1c r1d)).reverse - 1) * toMat Tag.E6.rank r1LY =
      (3 : ℤ) • (1 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) := by
  rw [wordMat_dc_inv_eq r1_a r1_ai r1_b r1_bi r1_c r1_ci r1_d r1_di]
  exact cert_of_lists (by decide +kernel)

end E6Data

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
