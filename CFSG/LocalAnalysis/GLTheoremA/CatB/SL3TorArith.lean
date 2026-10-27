module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.SL3Tor

theorem S_lt {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
    a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 - 1)) < b ^ 3 * ((b ^ 2 - 1) * (b ^ 3 - 1)) := by
  have h1 : a ^ 3 < b ^ 3 := Nat.pow_lt_pow_left hab (by norm_num)
  have h2 : a ^ 2 - 1 ≤ b ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hab.le 2) 1
  have h3 : a ^ 3 - 1 ≤ b ^ 3 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hab.le 3) 1
  have h4 : 4 ≤ a ^ 2 := by nlinarith
  have h5 : 8 ≤ a ^ 3 := by nlinarith
  have hpos : 0 < a ^ 2 - 1 := by omega
  have hpos' : 0 < a ^ 3 - 1 := by omega
  have h6 : (a ^ 2 - 1) * (a ^ 3 - 1) ≤ (b ^ 2 - 1) * (b ^ 3 - 1) := Nat.mul_le_mul h2 h3
  calc a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 - 1)) < b ^ 3 * ((a ^ 2 - 1) * (a ^ 3 - 1)) :=
        Nat.mul_lt_mul_of_pos_right h1 (Nat.mul_pos hpos hpos')
    _ ≤ b ^ 3 * ((b ^ 2 - 1) * (b ^ 3 - 1)) := Nat.mul_le_mul_left _ h6

theorem sl_card_inj {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 - 1)) = b ^ 3 * ((b ^ 2 - 1) * (b ^ 3 - 1))) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact absurd h (ne_of_lt (S_lt ha hlt))
  · exact heq
  · exact absurd h.symm (ne_of_lt (S_lt hb hgt))

theorem A_mono {x y : ℕ} (hxy : x ≤ y) :
    x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 + 1)) ≤ y ^ 3 * ((y ^ 2 - 1) * (y ^ 3 + 1)) := by
  have h1 : x ^ 3 ≤ y ^ 3 := Nat.pow_le_pow_left hxy 3
  have h2 : x ^ 2 - 1 ≤ y ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hxy 2) 1
  have h3 : x ^ 3 + 1 ≤ y ^ 3 + 1 := Nat.add_le_add_right h1 1
  exact Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)

theorem A_gt_B {N : ℕ} (hN : 2 ≤ N) :
    N ^ 3 * ((N ^ 2 - 1) * (N ^ 3 - 1)) < N ^ 3 * ((N ^ 2 - 1) * (N ^ 3 + 1)) := by
  have h4 : 4 ≤ N ^ 2 := by nlinarith
  have h5 : 8 ≤ N ^ 3 := by nlinarith
  have hpos : 0 < N ^ 2 - 1 := by omega
  refine Nat.mul_lt_mul_of_pos_left ?_ (by omega)
  refine Nat.mul_lt_mul_of_pos_left ?_ hpos
  omega

theorem A_lt_B_succ {M : ℕ} (hM : 2 ≤ M) :
    M ^ 3 * ((M ^ 2 - 1) * (M ^ 3 + 1)) < (M + 1) ^ 3 * (((M + 1) ^ 2 - 1) * ((M + 1) ^ 3 - 1)) := by
  have e2 : (M + 1) ^ 2 - 1 = M ^ 2 + 2 * M := by
    have : (M + 1) ^ 2 = (M ^ 2 + 2 * M) + 1 := by ring
    omega
  have e3 : (M + 1) ^ 3 - 1 = M ^ 3 + 3 * M ^ 2 + 3 * M := by
    have : (M + 1) ^ 3 = (M ^ 3 + 3 * M ^ 2 + 3 * M) + 1 := by ring
    omega
  have h1 : M ^ 3 < (M + 1) ^ 3 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  have h2 : M ^ 2 - 1 ≤ M ^ 2 + 2 * M := by omega
  have h3 : M ^ 3 + 1 < M ^ 3 + 3 * M ^ 2 + 3 * M := by nlinarith
  have hpos : 0 < M ^ 2 - 1 := by
    have : 4 ≤ M ^ 2 := by nlinarith
    omega
  rw [e2, e3]
  calc M ^ 3 * ((M ^ 2 - 1) * (M ^ 3 + 1))
      < (M + 1) ^ 3 * ((M ^ 2 - 1) * (M ^ 3 + 1)) :=
        Nat.mul_lt_mul_of_pos_right h1 (Nat.mul_pos hpos (by omega))
    _ ≤ (M + 1) ^ 3 * ((M ^ 2 + 2 * M) * (M ^ 3 + 1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2)
    _ < (M + 1) ^ 3 * ((M ^ 2 + 2 * M) * (M ^ 3 + 3 * M ^ 2 + 3 * M)) := by
        refine Nat.mul_lt_mul_of_pos_left ?_ (by positivity)
        exact Nat.mul_lt_mul_of_pos_left h3 (by positivity)

theorem su_sl_false {q N : ℕ} (hq : 2 ≤ q) (hN : 4 ≤ N) (hqm : q % 3 = 2) (hNm : N % 3 = 1)
    (h : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) = N ^ 3 * ((N ^ 2 - 1) * (N ^ 3 - 1))) : False := by
  have hne : q ≠ N := by omega
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hA := A_mono (show q ≤ M by omega)
    have hB := A_lt_B_succ (show 2 ≤ M by omega)
    linarith
  · have hA := A_mono (show N ≤ q by omega)
    have hB := A_gt_B (show 2 ≤ N by omega)
    linarith

end CFSG.LocalAnalysis.GLTheoremA.CatB.SL3Tor
