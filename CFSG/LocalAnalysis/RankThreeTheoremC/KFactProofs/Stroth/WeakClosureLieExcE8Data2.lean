module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcMat
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Four

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Blueprint.Chevalley CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
open scoped commutatorElement

set_option linter.unusedSectionVars false


namespace E8Data

@[expose] def r4a : List (Fin Tag.E8.rank) :=
  [4, 3, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 3, 2, 1, 3, 4, 2, 3, 0, 2, 1, 3]

@[expose] def r4b : List (Fin Tag.E8.rank) :=
  [0, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3, 1]

@[expose] def r4c : List (Fin Tag.E8.rank) :=
  [6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 4, 2, 1, 3, 0, 2, 1]

@[expose] def r4d : List (Fin Tag.E8.rank) :=
  [5, 6, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 6, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 3, 0, 2, 1, 3, 4, 5, 3, 4, 0, 2, 1, 3, 2, 1, 0]

@[expose] def r4LA : List (List ℤ) :=
  [[0, 1, 0, -1, 0, 0, 1, 1], [0, 1, 0, -2, 1, 0, 2, 0], [1, 2, 0, -3, 1, 0, 2, 1], [0, 3, 1, -5, 2, 0, 3, 1], [0, 3, 0, -4, 2, 0, 2, 1], [0, 2, 0, -3, 2, 0, 1, 1], [0, 1, 0, -2, 1, 1, 0, 1], [0, 1, 0, -1, 0, 1, 0, 0]]

@[expose] def r4LAi : List (List ℤ) :=
  [[0, 0, 1, 0, -2, 2, -1, 1], [1, 0, 0, 0, -2, 3, -2, 2], [1, 0, 0, 1, -4, 4, -2, 2], [2, 1, 0, 0, -5, 6, -3, 3], [1, 1, 0, 0, -4, 5, -2, 2], [1, 1, 0, 0, -3, 3, -1, 2], [1, 1, 0, 0, -2, 2, -1, 1], [1, 0, 0, 0, -1, 1, 0, 0]]

@[expose] def r4LB : List (List ℤ) :=
  [[1, -1, 0, 0, 0, -1, 2, -1], [2, -2, 0, 0, 0, -1, 2, 0], [2, -2, 1, -1, 0, -1, 3, -1], [3, -4, 1, -1, 1, -2, 4, -1], [3, -3, 1, -1, 1, -2, 3, -1], [3, -2, 0, -1, 1, -1, 2, -1], [2, -1, 0, -1, 1, -1, 1, 0], [1, -1, 0, 0, 0, 0, 0, 0]]

@[expose] def r4LBi : List (List ℤ) :=
  [[-1, 1, 0, -1, 1, 1, -1, -1], [-1, 1, 0, -1, 1, 1, -1, -2], [-2, 1, 0, -1, 2, 1, -2, -2], [-2, 2, -1, -1, 2, 2, -3, -3], [-2, 1, -1, 0, 1, 2, -2, -3], [-2, 1, 0, 0, 0, 2, -2, -2], [-1, 1, 0, 0, 0, 1, -1, -2], [-1, 1, 0, 0, 0, 0, 0, -1]]

@[expose] def r4LC : List (List ℤ) :=
  [[1, -1, -2, 2, 0, -1, 0, 1], [0, -1, -2, 2, 1, -2, 0, 2], [1, -1, -3, 3, 0, -2, 0, 3], [1, -2, -4, 4, 1, -4, 1, 4], [1, -1, -3, 3, 1, -4, 1, 3], [1, 0, -3, 2, 1, -3, 1, 2], [1, 0, -2, 1, 1, -2, 0, 2], [1, 0, -1, 0, 1, -1, 0, 1]]

@[expose] def r4LCi : List (List ℤ) :=
  [[0, 0, 1, -1, 1, 0, -2, 2], [-1, 1, 2, -2, 1, 1, -3, 2], [-1, 1, 2, -2, 2, 0, -4, 3], [-1, 2, 3, -3, 2, 1, -6, 4], [-1, 2, 2, -2, 1, 1, -5, 4], [-1, 1, 2, -1, 0, 1, -4, 3], [-1, 0, 1, 0, 0, 1, -3, 2], [-1, 0, 1, 0, 0, 0, -1, 1]]

@[expose] def r4LD : List (List ℤ) :=
  [[-1, -1, 0, 0, 2, -1, 0, -1], [-2, -2, 1, 0, 2, -1, 0, -1], [-3, -2, 1, 0, 3, -1, -1, -1], [-4, -4, 1, 1, 4, -2, -1, -1], [-3, -3, 1, 1, 3, -2, -1, -1], [-2, -2, 0, 1, 2, -1, -1, -1], [-1, -1, 0, 0, 2, -1, -1, 0], [-1, 0, 0, 0, 1, -1, 0, 0]]

@[expose] def r4LDi : List (List ℤ) :=
  [[1, -1, 0, 0, 1, -1, 0, -1], [1, -2, 1, 0, 1, -1, -1, 0], [1, -2, 1, 0, 2, -2, -1, -1], [2, -4, 1, 1, 2, -2, -2, -1], [2, -3, 1, 1, 1, -2, -1, -1], [1, -2, 1, 1, 0, -1, -1, -1], [1, -1, 0, 1, 0, -1, -1, 0], [0, -1, 0, 1, 0, -1, 0, 0]]

@[expose] def r4LW : List (List ℤ) :=
  [[-2, 0, 0, 0, 1, 0, 0, 0], [-3, 0, 0, 0, 1, 0, 1, -1], [-4, 0, 0, 0, 1, 1, 0, 0], [-6, 0, 0, 0, 2, 0, 1, 0], [-5, 0, 0, 0, 2, 0, 0, 0], [-3, 0, -1, 0, 2, 0, 0, 0], [-2, 0, 0, -1, 2, 0, 0, 0], [-1, 1, 0, -1, 1, 0, 0, 0]]

theorem r4_a : wordMat Tag.E8 r4a = toMat Tag.E8.rank r4LA :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r4_ai : wordMat Tag.E8 r4a.reverse = toMat Tag.E8.rank r4LAi :=
  wordMat_reverse_eq r4_a (by decide +kernel)

theorem r4_b : wordMat Tag.E8 r4b = toMat Tag.E8.rank r4LB :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r4_bi : wordMat Tag.E8 r4b.reverse = toMat Tag.E8.rank r4LBi :=
  wordMat_reverse_eq r4_b (by decide +kernel)

theorem r4_c : wordMat Tag.E8 r4c = toMat Tag.E8.rank r4LC :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r4_ci : wordMat Tag.E8 r4c.reverse = toMat Tag.E8.rank r4LCi :=
  wordMat_reverse_eq r4_c (by decide +kernel)

theorem r4_d : wordMat Tag.E8 r4d = toMat Tag.E8.rank r4LD :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r4_di : wordMat Tag.E8 r4d.reverse = toMat Tag.E8.rank r4LDi :=
  wordMat_reverse_eq r4_d (by decide +kernel)

theorem r4_w : wordMat Tag.E8 e8FourWord = toMat Tag.E8.rank r4LW :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem r4_dc :
    wordMat Tag.E8 (cw (cw r4a r4b) (cw r4c r4d)) =
      (-1 : ℤ) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) := by
  have h := dc_eq_smul_pow (w := ([] : List (Fin Tag.E8.rank))) r4_a r4_ai r4_b r4_bi r4_c r4_ci r4_d r4_di (W := lid Tag.E8.rank) (s := -1) (k := 0)
    (by rw [wordMat_nil, toMat_lid]) (by decide +kernel)
  rwa [pow_zero] at h

theorem r4_comm_a :
    wordMat Tag.E8 r4a * wordMat Tag.E8 e8FourWord = wordMat Tag.E8 e8FourWord * wordMat Tag.E8 r4a :=
  comm_of_lists r4_a r4_w (by decide +kernel)

theorem r4_comm_b :
    wordMat Tag.E8 r4b * wordMat Tag.E8 e8FourWord = wordMat Tag.E8 e8FourWord * wordMat Tag.E8 r4b :=
  comm_of_lists r4_b r4_w (by decide +kernel)

theorem r4_comm_c :
    wordMat Tag.E8 r4c * wordMat Tag.E8 e8FourWord = wordMat Tag.E8 e8FourWord * wordMat Tag.E8 r4c :=
  comm_of_lists r4_c r4_w (by decide +kernel)

theorem r4_comm_d :
    wordMat Tag.E8 r4d * wordMat Tag.E8 e8FourWord = wordMat Tag.E8 e8FourWord * wordMat Tag.E8 r4d :=
  comm_of_lists r4_d r4_w (by decide +kernel)

@[expose] def r4LWi : List (List ℤ) :=
  [[2, 0, 0, 0, -1, 0, 0, 0], [3, 0, 0, 0, -1, 0, -1, 1], [4, 0, 0, 0, -1, -1, 0, 0], [6, 0, 0, 0, -2, 0, -1, 0], [5, 0, 0, 0, -2, 0, 0, 0], [3, 0, 1, 0, -2, 0, 0, 0], [2, 0, 0, 1, -2, 0, 0, 0], [1, -1, 0, 1, -1, 0, 0, 0]]

theorem r4_wi : wordMat Tag.E8 e8FourWord.reverse = toMat Tag.E8.rank r4LWi :=
  wordMat_reverse_eq r4_w (by decide +kernel)

@[expose] def sx : List (Fin Tag.E8.rank) :=
  [5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 5, 4, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 4, 2, 1, 3, 0]

@[expose] def SXM : List (List ℤ) :=
  [[-1, 1, 1, -1, 1, -1, 0, -1], [-1, 0, 2, -1, 1, -1, 0, -2], [-2, 1, 2, -1, 1, -1, 0, -3], [-2, 1, 3, -1, 1, -2, 0, -4], [-2, 1, 3, -1, 0, -1, 0, -3], [-2, 0, 2, 0, 0, -1, 0, -2], [-2, 0, 2, 0, 0, -1, 0, -1], [-1, 0, 1, 0, 0, -1, 1, -1]]

@[expose] def SXMi : List (List ℤ) :=
  [[-1, 0, 0, 1, 0, -2, 1, 0], [-1, -1, 1, 1, 0, -3, 2, 0], [-2, 0, 1, 1, 0, -4, 3, 0], [-3, -1, 2, 2, -1, -5, 4, 0], [-2, 0, 2, 1, -1, -4, 3, 0], [-2, 0, 2, 0, 0, -3, 2, 0], [-1, 0, 1, 0, 0, -2, 1, 1], [0, 0, 0, 0, 0, -1, 1, 0]]

theorem sx_m : wordMat Tag.E8 sx = toMat Tag.E8.rank SXM :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem sx_mi : wordMat Tag.E8 sx.reverse = toMat Tag.E8.rank SXMi :=
  wordMat_reverse_eq sx_m (by decide +kernel)

theorem sx_comm :
    wordMat Tag.E8 sx * wordMat Tag.E8 e8FourWord = wordMat Tag.E8 e8FourWord * wordMat Tag.E8 sx :=
  comm_of_lists sx_m r4_w (by decide +kernel)

@[expose] def sy : List (Fin Tag.E8.rank) :=
  [0, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4, 1, 3, 2, 1]

@[expose] def SYM : List (List ℤ) :=
  [[1, -1, -1, 1, -1, 1, -1, 1], [2, -1, -2, 2, -2, 1, -1, 2], [3, -1, -3, 2, -2, 2, -2, 2], [4, -1, -4, 3, -3, 2, -3, 4], [4, -1, -3, 2, -2, 1, -2, 3], [3, -1, -3, 2, -1, 0, -1, 2], [2, 0, -2, 1, -1, 0, 0, 1], [1, 0, -1, 1, -1, 0, 0, 0]]

@[expose] def SYMi : List (List ℤ) :=
  [[-2, 1, 1, -1, 1, 0, -1, 0], [-3, 1, 1, 0, 0, 0, -1, 0], [-3, 2, 1, -1, 1, 0, -2, 0], [-5, 3, 2, -1, 0, 1, -3, 0], [-4, 2, 2, -1, 0, 1, -2, -1], [-3, 2, 2, -1, 0, 0, -1, -1], [-2, 2, 1, -1, 0, 0, 0, -1], [-1, 1, 0, 0, 0, 0, 0, -1]]

theorem sy_m : wordMat Tag.E8 sy = toMat Tag.E8.rank SYM :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem sy_mi : wordMat Tag.E8 sy.reverse = toMat Tag.E8.rank SYMi :=
  wordMat_reverse_eq sy_m (by decide +kernel)

theorem sy_comm :
    wordMat Tag.E8 sy * wordMat Tag.E8 e8FourWord = wordMat Tag.E8 e8FourWord * wordMat Tag.E8 sy :=
  comm_of_lists sy_m r4_w (by decide +kernel)

@[expose] def ss : List (Fin Tag.E8.rank) :=
  [4, 5, 6, 7, 1, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 4, 5, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 2, 3, 0, 2, 1, 3, 0, 2, 0]

@[expose] def SSM : List (List ℤ) :=
  [[-2, 0, 0, 0, 1, 0, 0, 0], [-3, 0, 0, 0, 1, 0, 1, -1], [-4, 0, 0, 0, 1, 1, 0, 0], [-6, 0, 0, 0, 2, 0, 1, 0], [-5, 0, 0, 0, 2, 0, 0, 0], [-3, 0, -1, 0, 2, 0, 0, 0], [-2, 0, 0, -1, 2, 0, 0, 0], [-1, 1, 0, -1, 1, 0, 0, 0]]

@[expose] def SSMi : List (List ℤ) :=
  [[2, 0, 0, 0, -1, 0, 0, 0], [3, 0, 0, 0, -1, 0, -1, 1], [4, 0, 0, 0, -1, -1, 0, 0], [6, 0, 0, 0, -2, 0, -1, 0], [5, 0, 0, 0, -2, 0, 0, 0], [3, 0, 1, 0, -2, 0, 0, 0], [2, 0, 0, 1, -2, 0, 0, 0], [1, -1, 0, 1, -1, 0, 0, 0]]

theorem ss_m : wordMat Tag.E8 ss = toMat Tag.E8.rank SSM :=
  wordMat_eq_toMat _ _ (by decide +kernel)

theorem ss_mi : wordMat Tag.E8 ss.reverse = toMat Tag.E8.rank SSMi :=
  wordMat_reverse_eq ss_m (by decide +kernel)

theorem ss_comm :
    wordMat Tag.E8 ss * wordMat Tag.E8 e8FourWord = wordMat Tag.E8 e8FourWord * wordMat Tag.E8 ss :=
  comm_of_lists ss_m r4_w (by decide +kernel)

theorem s4_pow : wordMat Tag.E8 (cw sx sy) ^ 5 = 1 :=
  cw_pow_of_lists sx_m sx_mi sy_m sy_mi (by decide +kernel)

theorem s4_hvec2 :
    ∀ j : Fin Tag.E8.rank, (5 : ℤ) ∣ 2 * (∑ i, (fun i : Fin Tag.E8.rank => (![2, -2, 0, 2, 0, 0, 0, 1] : Fin 8 → ℤ) i) i *
      weylMat (wp Tag.E8 e8FourWord)⁻¹ i j) - (fun i : Fin Tag.E8.rank => (![2, -2, 0, 2, 0, 0, 0, 1] : Fin 8 → ℤ) i) j := by
  rw [weylMat_wp_inv, r4_wi]
  decide +kernel

theorem s4_hj2 :
    ¬ (5 : ℤ) ∣ ∑ i, (fun i : Fin Tag.E8.rank => (![2, -2, 0, 2, 0, 0, 0, 1] : Fin 8 → ℤ) i) i *
      ((weylMat (wp Tag.E8 ss)⁻¹ - 1) * (weylMat ⁅wp Tag.E8 sx, wp Tag.E8 sy⁆⁻¹ - 1)) i 0 := by
  rw [weylMat_wp_inv, weylMat_cw_inv, cw_reverse, wordMat_cw_eq sy_m sy_mi sx_m sx_mi, ss_mi]
  decide +kernel

theorem s4_hvec3 :
    ∀ j : Fin Tag.E8.rank, (5 : ℤ) ∣ 3 * (∑ i, (fun i : Fin Tag.E8.rank => (![1, 2, 0, -2, 0, 0, 0, 1] : Fin 8 → ℤ) i) i *
      weylMat (wp Tag.E8 e8FourWord)⁻¹ i j) - (fun i : Fin Tag.E8.rank => (![1, 2, 0, -2, 0, 0, 0, 1] : Fin 8 → ℤ) i) j := by
  rw [weylMat_wp_inv, r4_wi]
  decide +kernel

theorem s4_hj3 :
    ¬ (5 : ℤ) ∣ ∑ i, (fun i : Fin Tag.E8.rank => (![1, 2, 0, -2, 0, 0, 0, 1] : Fin 8 → ℤ) i) i *
      ((weylMat (wp Tag.E8 ss)⁻¹ - 1) * (weylMat ⁅wp Tag.E8 sx, wp Tag.E8 sy⁆⁻¹ - 1)) i 0 := by
  rw [weylMat_wp_inv, weylMat_cw_inv, cw_reverse, wordMat_cw_eq sy_m sy_mi sx_m sx_mi, ss_mi]
  decide +kernel

end E8Data

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
