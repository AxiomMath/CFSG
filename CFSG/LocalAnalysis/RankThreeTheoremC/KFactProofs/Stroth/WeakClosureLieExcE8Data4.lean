module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcMat
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Ten
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Twelve

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
open scoped commutatorElement

set_option linter.unusedSectionVars false


namespace E8Data

@[expose] def r10a : List (Fin Tag.E8.rank) :=
  [3, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2, 1, 3, 4, 3, 2, 1]

@[expose] def r10b : List (Fin Tag.E8.rank) :=
  [2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 0, 2, 1, 3, 4, 5, 4, 2, 3, 0, 2, 1, 3, 4, 3, 1, 0]

@[expose] def r10c : List (Fin Tag.E8.rank) :=
  [6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 2, 1, 3, 1, 0]

@[expose] def r10d : List (Fin Tag.E8.rank) :=
  [2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 1, 3, 4, 5, 4, 3, 0, 2, 1, 3, 4, 1, 3, 2, 1, 0]

@[expose] def r10LA : List (List ℤ) :=
  [[1, -1, -1, 2, -2, 0, 1, 0], [2, -1, -1, 2, -3, 1, 1, -1], [3, -2, -2, 3, -3, 0, 2, -1], [4, -3, -2, 4, -5, 1, 2, -1], [3, -3, -1, 3, -4, 1, 2, -1], [2, -2, -1, 2, -3, 1, 2, -1], [1, -2, -1, 2, -2, 1, 1, -1], [0, -1, 0, 1, -1, 0, 1, -1]]

@[expose] def r10LAi : List (List ℤ) :=
  [[0, 1, 1, -2, 2, -1, 0, -1], [1, 2, 1, -3, 2, -1, 0, -1], [1, 2, 1, -4, 4, -2, 0, -1], [2, 3, 2, -6, 5, -3, 1, -2], [1, 2, 2, -5, 4, -2, 1, -2], [1, 2, 1, -4, 3, -1, 1, -2], [1, 1, 1, -3, 2, 0, 0, -1], [1, 0, 0, -1, 1, 0, 0, -1]]

@[expose] def r10LB : List (List ℤ) :=
  [[0, -1, 1, 1, -2, 1, 0, -1], [0, -1, 2, 0, -2, 2, -1, -1], [0, -2, 2, 1, -3, 2, 0, -2], [-1, -3, 4, 1, -4, 3, -1, -2], [-1, -2, 4, 0, -3, 2, 0, -2], [-1, -1, 3, 0, -3, 2, 0, -1], [-1, -1, 2, 0, -2, 2, 0, -1], [-1, 0, 1, 0, -1, 1, 0, -1]]

@[expose] def r10LBi : List (List ℤ) :=
  [[2, 1, -1, -1, 1, -1, 1, -1], [3, 1, -2, -1, 1, -1, 1, 0], [4, 1, -3, -1, 2, -2, 2, -1], [6, 1, -4, -1, 2, -3, 3, -1], [4, 1, -3, -1, 2, -3, 3, -1], [3, 1, -2, -1, 1, -2, 3, -1], [2, 0, -1, -1, 1, -1, 2, -1], [1, 0, -1, 0, 0, 0, 1, -1]]

@[expose] def r10LC : List (List ℤ) :=
  [[0, 0, 1, -1, 0, 0, 0, 0], [-1, 0, 1, 0, -1, 0, 0, 0], [0, -1, 1, 0, -1, 0, 0, 0], [-1, -1, 2, 0, -2, 1, -1, 0], [-1, -1, 1, 0, -1, 1, -1, 0], [-1, -1, 1, 0, -1, 1, 0, -1], [-1, -1, 1, 0, 0, 0, 0, -1], [-1, -1, 1, 0, 0, 0, 0, 0]]

@[expose] def r10LCi : List (List ℤ) :=
  [[0, -1, 0, 1, -1, 0, 0, 0], [0, 0, -1, 1, -1, 0, 0, 0], [0, -1, -1, 2, -2, 0, 0, 1], [-1, -1, -1, 2, -2, 0, 0, 1], [0, -1, -1, 1, -1, 0, 0, 1], [0, -1, -1, 1, -1, 1, -1, 1], [0, 0, 0, 0, -1, 1, -1, 1], [0, 0, 0, 0, 0, 0, -1, 1]]

@[expose] def r10LD : List (List ℤ) :=
  [[-2, 0, 1, 0, 0, 0, -1, 1], [-3, 0, 1, 1, -1, 1, -2, 1], [-4, -1, 2, 1, -1, 1, -2, 1], [-6, -1, 3, 1, -1, 2, -4, 2], [-5, -1, 2, 1, -1, 2, -3, 2], [-4, 0, 2, 0, -1, 2, -2, 1], [-3, 0, 1, 0, 0, 1, -1, 0], [-2, 0, 1, 0, 0, 0, 0, 0]]

@[expose] def r10LDi : List (List ℤ) :=
  [[-1, 0, -1, 1, 0, 0, -1, 1], [-1, 1, -2, 1, 0, 0, -1, 2], [-2, 0, -2, 2, 0, 0, -2, 3], [-3, 1, -3, 2, 1, -1, -2, 4], [-2, 0, -3, 2, 1, -1, -1, 3], [-2, 0, -2, 1, 1, 0, -1, 2], [-1, 0, -1, 0, 1, 0, -1, 2], [0, 0, -1, 0, 1, 0, -1, 1]]

@[expose] def r10LW : List (List ℤ) :=
  [[0, 0, 1, -1, 1, 0, 0, -1], [-1, 0, 2, -1, 1, 0, -1, 0], [-1, 0, 3, -2, 1, 1, -1, -1], [-2, 0, 4, -2, 1, 1, -1, -1], [-2, 1, 3, -2, 1, 1, -1, -1], [-1, 1, 2, -1, 0, 1, -1, -1], [0, 1, 1, -1, 0, 1, -1, 0], [0, 0, 0, 0, 0, 1, -1, 0]]

theorem r10_a : wordMat Tag.E8 r10a = toMat Tag.E8.rank r10LA :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r10_ai : wordMat Tag.E8 r10a.reverse = toMat Tag.E8.rank r10LAi :=
  wordMat_reverse_eq r10_a (by decide +kernel)

theorem r10_b : wordMat Tag.E8 r10b = toMat Tag.E8.rank r10LB :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r10_bi : wordMat Tag.E8 r10b.reverse = toMat Tag.E8.rank r10LBi :=
  wordMat_reverse_eq r10_b (by decide +kernel)

theorem r10_c : wordMat Tag.E8 r10c = toMat Tag.E8.rank r10LC :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r10_ci : wordMat Tag.E8 r10c.reverse = toMat Tag.E8.rank r10LCi :=
  wordMat_reverse_eq r10_c (by decide +kernel)

theorem r10_d : wordMat Tag.E8 r10d = toMat Tag.E8.rank r10LD :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r10_di : wordMat Tag.E8 r10d.reverse = toMat Tag.E8.rank r10LDi :=
  wordMat_reverse_eq r10_d (by decide +kernel)

theorem r10_w : wordMat Tag.E8 e8TenWord = toMat Tag.E8.rank r10LW :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r10_dc :
    wordMat Tag.E8 (cw (cw r10a r10b) (cw r10c r10d)) =
      (-1 : ℤ) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) := by
  have h := dc_eq_smul_pow (w := ([] : List (Fin Tag.E8.rank))) r10_a r10_ai r10_b r10_bi r10_c r10_ci r10_d r10_di (W := lid Tag.E8.rank) (s := -1) (k := 0)
    (by rw [wordMat_nil, toMat_lid]) (by decide +kernel)
  rwa [pow_zero] at h

theorem r10_comm_a :
    wordMat Tag.E8 r10a * wordMat Tag.E8 e8TenWord = wordMat Tag.E8 e8TenWord * wordMat Tag.E8 r10a :=
  comm_of_lists r10_a r10_w (by decide +kernel)

theorem r10_comm_b :
    wordMat Tag.E8 r10b * wordMat Tag.E8 e8TenWord = wordMat Tag.E8 e8TenWord * wordMat Tag.E8 r10b :=
  comm_of_lists r10_b r10_w (by decide +kernel)

theorem r10_comm_c :
    wordMat Tag.E8 r10c * wordMat Tag.E8 e8TenWord = wordMat Tag.E8 e8TenWord * wordMat Tag.E8 r10c :=
  comm_of_lists r10_c r10_w (by decide +kernel)

theorem r10_comm_d :
    wordMat Tag.E8 r10d * wordMat Tag.E8 e8TenWord = wordMat Tag.E8 e8TenWord * wordMat Tag.E8 r10d :=
  comm_of_lists r10_d r10_w (by decide +kernel)

@[expose] def r12a : List (Fin Tag.E8.rank) :=
  [2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 6, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 2, 1, 3, 4, 5, 3, 2, 1, 3, 4, 0, 2, 1, 3, 1]

@[expose] def r12b : List (Fin Tag.E8.rank) :=
  [3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 4, 5, 3, 2, 1, 3, 4, 2, 3, 0, 2, 1]

@[expose] def r12c : List (Fin Tag.E8.rank) :=
  [1, 3, 4, 5, 6, 7, 6, 5, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 3, 0, 2, 1, 3, 4, 2, 3, 0, 2, 0]

@[expose] def r12d : List (Fin Tag.E8.rank) :=
  [3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 5, 6, 1, 3, 4, 5, 2, 1, 3, 4, 2, 1, 3, 1]

@[expose] def r12LA : List (List ℤ) :=
  [[0, -1, 1, -1, 1, 0, 0, -1], [0, -2, 1, 0, 0, 1, -1, -1], [1, -2, 1, -1, 1, 1, -1, -2], [1, -4, 2, -1, 1, 2, -2, -2], [1, -3, 2, -1, 1, 1, -2, -1], [1, -3, 1, 0, 1, 0, -1, -1], [1, -2, 0, 0, 1, 0, -1, 0], [0, -1, 0, 0, 1, 0, -1, 0]]

@[expose] def r12LAi : List (List ℤ) :=
  [[-1, -2, 0, 1, 0, 1, -1, 0], [-1, -2, 0, 1, 0, 1, -2, 1], [-1, -3, -1, 2, 0, 2, -3, 1], [-2, -4, -1, 3, -1, 3, -4, 2], [-1, -4, -1, 3, -1, 2, -3, 2], [-1, -3, -1, 3, -1, 1, -2, 1], [0, -2, -1, 2, -1, 1, -1, 0], [0, -1, -1, 1, 0, 0, 0, 0]]

@[expose] def r12LB : List (List ℤ) :=
  [[0, -1, -1, 1, 0, 1, -2, 1], [0, -1, -1, 2, -1, 1, -3, 2], [0, -2, -2, 3, -1, 1, -3, 2], [1, -2, -3, 4, -2, 2, -5, 3], [1, -1, -3, 3, -1, 1, -4, 3], [1, -1, -2, 2, -1, 1, -3, 3], [1, -1, -2, 2, -1, 1, -2, 2], [1, -1, -1, 1, 0, 0, -1, 1]]

@[expose] def r12LBi : List (List ℤ) :=
  [[0, 1, -1, 0, 0, -1, 1, 1], [0, 2, -1, -1, 1, -2, 2, 0], [0, 3, -1, -1, 0, -2, 2, 1], [0, 4, -1, -2, 1, -4, 4, 1], [1, 3, -1, -2, 1, -3, 3, 1], [1, 2, -1, -1, 0, -2, 3, 0], [0, 1, 0, -1, 0, -1, 2, 0], [0, 1, 0, -1, 0, 0, 1, 0]]

@[expose] def r12LC : List (List ℤ) :=
  [[0, 1, -1, 1, -1, 0, 0, 1], [-1, 2, -1, 1, -1, -1, 1, 1], [-1, 2, -1, 1, -1, -1, 1, 2], [-2, 3, -2, 2, -2, -1, 2, 2], [-1, 3, -2, 1, -1, -1, 2, 1], [-1, 3, -1, 0, -1, 0, 1, 1], [0, 2, -1, 0, -1, 0, 1, 1], [0, 1, -1, 0, 0, 0, 0, 1]]

@[expose] def r12LCi : List (List ℤ) :=
  [[1, -1, 1, -1, 1, 0, 0, -1], [1, -1, 1, -1, 1, 1, -1, -1], [1, -2, 2, -1, 1, 1, -1, -2], [2, -3, 2, -1, 2, 1, -2, -2], [1, -3, 2, -1, 2, 1, -2, -1], [1, -3, 1, 0, 1, 1, -1, -1], [0, -2, 1, 0, 1, 0, 0, -1], [0, -1, 1, 0, 0, 0, 0, 0]]

@[expose] def r12LD : List (List ℤ) :=
  [[1, 0, 1, -1, 0, 0, 1, -2], [2, -1, 1, -1, 0, 1, 0, -2], [2, -1, 2, -2, 1, 0, 1, -3], [3, -2, 2, -2, 1, 1, 1, -5], [2, -2, 2, -1, 0, 1, 1, -4], [1, -1, 2, -1, 0, 1, 0, -3], [1, -1, 1, 0, 0, 0, 0, -2], [0, -1, 1, 0, 0, 0, 0, -1]]

@[expose] def r12LDi : List (List ℤ) :=
  [[-1, 0, 1, -1, 1, 0, 1, -2], [-1, -1, 1, -1, 1, 1, 1, -3], [-2, -1, 2, -2, 2, 1, 1, -3], [-3, -2, 2, -2, 3, 1, 2, -5], [-3, -2, 2, -1, 2, 1, 1, -4], [-2, -1, 1, -1, 2, 1, 0, -3], [-1, -1, 1, -1, 2, 0, 0, -2], [-1, 0, 1, -1, 1, 0, 0, -1]]

@[expose] def r12LW : List (List ℤ) :=
  [[-1, 0, 1, 0, 0, 0, 0, 0], [-2, 0, 1, 0, 0, 0, 1, 0], [-2, 0, 1, 0, 0, 1, 0, 0], [-4, 0, 2, 0, 0, 1, 0, 1], [-4, 0, 2, 0, 0, 1, 0, 0], [-3, 0, 1, 0, 1, 0, 0, 0], [-2, 1, 1, -1, 1, 0, 0, 0], [-1, 1, 0, 0, 0, 0, 0, 0]]

theorem r12_a : wordMat Tag.E8 r12a = toMat Tag.E8.rank r12LA :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r12_ai : wordMat Tag.E8 r12a.reverse = toMat Tag.E8.rank r12LAi :=
  wordMat_reverse_eq r12_a (by decide +kernel)

theorem r12_b : wordMat Tag.E8 r12b = toMat Tag.E8.rank r12LB :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r12_bi : wordMat Tag.E8 r12b.reverse = toMat Tag.E8.rank r12LBi :=
  wordMat_reverse_eq r12_b (by decide +kernel)

theorem r12_c : wordMat Tag.E8 r12c = toMat Tag.E8.rank r12LC :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r12_ci : wordMat Tag.E8 r12c.reverse = toMat Tag.E8.rank r12LCi :=
  wordMat_reverse_eq r12_c (by decide +kernel)

theorem r12_d : wordMat Tag.E8 r12d = toMat Tag.E8.rank r12LD :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r12_di : wordMat Tag.E8 r12d.reverse = toMat Tag.E8.rank r12LDi :=
  wordMat_reverse_eq r12_d (by decide +kernel)

theorem r12_w : wordMat Tag.E8 e8TwelveWord = toMat Tag.E8.rank r12LW :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r12_dc :
    wordMat Tag.E8 (cw (cw r12a r12b) (cw r12c r12d)) =
      (-1 : ℤ) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) := by
  have h := dc_eq_smul_pow (w := ([] : List (Fin Tag.E8.rank))) r12_a r12_ai r12_b r12_bi r12_c r12_ci r12_d r12_di (W := lid Tag.E8.rank) (s := -1) (k := 0)
    (by rw [wordMat_nil, toMat_lid]) (by decide +kernel)
  rwa [pow_zero] at h

theorem r12_comm_a :
    wordMat Tag.E8 r12a * wordMat Tag.E8 e8TwelveWord = wordMat Tag.E8 e8TwelveWord * wordMat Tag.E8 r12a :=
  comm_of_lists r12_a r12_w (by decide +kernel)

theorem r12_comm_b :
    wordMat Tag.E8 r12b * wordMat Tag.E8 e8TwelveWord = wordMat Tag.E8 e8TwelveWord * wordMat Tag.E8 r12b :=
  comm_of_lists r12_b r12_w (by decide +kernel)

theorem r12_comm_c :
    wordMat Tag.E8 r12c * wordMat Tag.E8 e8TwelveWord = wordMat Tag.E8 e8TwelveWord * wordMat Tag.E8 r12c :=
  comm_of_lists r12_c r12_w (by decide +kernel)

theorem r12_comm_d :
    wordMat Tag.E8 r12d * wordMat Tag.E8 e8TwelveWord = wordMat Tag.E8 e8TwelveWord * wordMat Tag.E8 r12d :=
  comm_of_lists r12_d r12_w (by decide +kernel)

end E8Data

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
