module

public import Certificates.Data.CFSGNative.F4.Unitary
import CFSG.Fischer.UnitaryCode
import all CFSG.Fischer.F4
public import Mathlib.Data.Nat.Notation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.KC.Misc.Lines

open CFSG.F4.Native CFSG.Fischer

theorem f4mul_lt (x y : ℕ) : f4mul x y < 4 := by
  unfold f4mul
  dsimp only
  omega

theorem scaleC_lt (a c : ℕ) : scaleC a c < 4096 := by
  unfold scaleC
  rw [foldl_add_six]
  have h0 := f4mul_lt a (coord c 0)
  have h1 := f4mul_lt a (coord c 1)
  have h2 := f4mul_lt a (coord c 2)
  have h3 := f4mul_lt a (coord c 3)
  have h4 := f4mul_lt a (coord c 4)
  have h5 := f4mul_lt a (coord c 5)
  norm_num
  omega

theorem normC_lt (c : ℕ) : normC c < 4096 := scaleC_lt _ _

theorem xor_lt_4096 {a b : ℕ} (ha : a < 4096) (hb : b < 4096) : a ^^^ b < 4096 :=
  Nat.xor_lt_two_pow (n := 12) ha hb

theorem scaleC_zero (c : ℕ) : scaleC 0 c = 0 := by
  unfold scaleC
  simp [f4mul, List.range_succ]

private theorem codeOf_vecOfCode' {c : ℕ} (hc : c < 4096) : codeOf (vecOfCode c) = c := by
  show c / 4 ^ 0 % 4 + 4 * (c / 4 ^ 1 % 4) + 16 * (c / 4 ^ 2 % 4) + 64 * (c / 4 ^ 3 % 4) +
    256 * (c / 4 ^ 4 % 4) + 1024 * (c / 4 ^ 5 % 4) = c
  norm_num
  omega

private theorem eq_of_codeOf_eq {v w : Fin 6 → F4} (h : codeOf v = codeOf w) : v = w := by
  rw [← vecOfCode_codeOf v, ← vecOfCode_codeOf w, h]

private theorem hermStd_comm (x y : Fin 6 → F4) : hermStd y x = (hermStd x y) ^ 2 := by
  have add_sq : ∀ a b : F4, (a + b) ^ 2 = a ^ 2 + b ^ 2 := by decide
  have fr : ∀ a b : F4, (a * b ^ 2) ^ 2 = a ^ 2 * b := by decide
  unfold hermStd
  rw [Fin.sum_univ_six, Fin.sum_univ_six, add_sq, add_sq, add_sq, add_sq, add_sq]
  simp only [fr]
  ring

theorem hermC_zero_comm {c d : ℕ} (hc : c < 4096) (hd : d < 4096) :
    hermC c d = 0 ↔ hermC d c = 0 := by
  have e1 : hermC c d = (hermStd (vecOfCode c) (vecOfCode d)).code.val := by
    rw [← hermC_codeOf, codeOf_vecOfCode' hc, codeOf_vecOfCode' hd]
  have e2 : hermC d c = (hermStd (vecOfCode d) (vecOfCode c)).code.val := by
    rw [← hermC_codeOf, codeOf_vecOfCode' hc, codeOf_vecOfCode' hd]
  rw [e1, e2, code_eq_zero_iff, code_eq_zero_iff, hermStd_comm (vecOfCode c) (vecOfCode d)]
  exact (pow_eq_zero_iff (by norm_num)).symm

private theorem hermStd_smul_right (x y : Fin 6 → F4) (s : F4) :
    hermStd x (s • y) = s ^ 2 * hermStd x y := by
  unfold hermStd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem cube_one : ∀ c : F4, c ≠ 0 → c * c * c = 1 := by decide

private theorem herm_zero_of_normV_tv {x u : Fin 6 → F4} (hx : x ≠ 0) (hxi : hermStd x x = 0)
    (h : normV (x + hermStd x u • u) = x) : hermStd x u = 0 := by
  by_contra ha
  set a := hermStd x u with ha_def
  set w : Fin 6 → F4 := x + a • u with hw
  have hl : lead w * lead w ≠ 0 := by
    intro h0
    apply hx
    rw [← h]
    unfold normV
    rw [h0, zero_smul]
  have hl' : lead w ≠ 0 := fun h0 => hl (by rw [h0, mul_zero])
  have hw' : w = lead w • x := by
    rw [← h]
    unfold normV
    rw [smul_smul, show lead w * (lead w * lead w) = lead w * lead w * lead w by ring,
      cube_one _ hl', one_smul]
  have hau : a • u = (lead w + 1) • x := by
    have key : ∀ p q r : F4, p + q = r → q = r + p := by decide
    funext i
    have h1 : x i + a * u i = lead w * x i := by
      have := congrFun hw' i
      simpa [hw] using this
    have h2 := key _ _ _ h1
    simp only [Pi.smul_apply, smul_eq_mul, add_mul, one_mul]
    exact h2
  have h3 := congrArg (hermStd x) hau
  rw [hermStd_smul_right, hermStd_smul_right, hxi, mul_zero, ← ha_def] at h3
  exact ha (by
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact (pow_eq_zero_iff (by norm_num)).1 h4
    · exact h4)

theorem normC_tvC_eq_iff {c v : ℕ} (hc : c < 4096) (hv : v < 4096) (hc0 : c ≠ 0)
    (hci : hermC c c = 0) (hn : normC c = c) : normC (tvC v c) = c ↔ hermC c v = 0 := by
  constructor
  · intro h
    have hcx : codeOf (vecOfCode c) = c := codeOf_vecOfCode' hc
    have hvu : codeOf (vecOfCode v) = v := codeOf_vecOfCode' hv
    have hx0 : vecOfCode c ≠ 0 := by
      intro h0
      apply hc0
      rw [← hcx, h0]
      decide
    have hxi : hermStd (vecOfCode c) (vecOfCode c) = 0 := by
      have : hermC c c = (hermStd (vecOfCode c) (vecOfCode c)).code.val := by
        rw [← hermC_codeOf, hcx]
      rw [this] at hci
      exact (code_eq_zero_iff _).1 hci
    have hh : hermC c v = (hermStd (vecOfCode c) (vecOfCode v)).code.val := by
      rw [← hermC_codeOf, hcx, hvu]
    rw [hh, code_eq_zero_iff]
    apply herm_zero_of_normV_tv hx0 hxi
    apply eq_of_codeOf_eq
    rw [← normC_codeOf, ← tvC_codeOf, hcx, hvu, h]
  · intro h
    unfold tvC addC
    rw [h, scaleC_zero]
    simpa using hn

end CFSG.KC.Misc.Lines

end
