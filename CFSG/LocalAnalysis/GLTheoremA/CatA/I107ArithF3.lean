module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

theorem rk2Cnt_twB2_le_one (m : ℕ) : rk2Cnt [(1, true), (2, false)] m ≤ 1 := by
  unfold rk2Cnt
  by_cases h1 : m ∣ 1
  · have hm : m = 1 := Nat.dvd_one.1 h1
    subst hm
    simp
  · simp [List.countP_cons, h1]
    split_ifs <;> norm_num

theorem arith0_kill (c R n r e : ℕ) (hn : 1 ≤ n) (he : e ≤ 1) (hn1 : n = 1 → e = 0) (hr : r ≤ R)
    (hR : R + 2 < c) (hg : c * n ≤ r + e + 2) : False := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    have := hn1 rfl
    subst this
    omega
  · have h2 : 2 * c ≤ c * n := by nlinarith
    omega

theorem arith_G2 (n r e : ℕ) (hn : 2 ≤ n) (he : e ≤ 1) (hr : r ≤ 2) (hg : 3 * n ≤ r + e + 2) : False := by
  omega

theorem arith_twF4 (n r e : ℕ) (hn : 3 ≤ n) (he : e ≤ 1) (hr : r ≤ 2) (hg : 2 * n ≤ r + e + 2) : False := by
  omega

theorem arith_triD4 (n r e b : ℕ) (hn : 1 ≤ n) (he : e ≤ 1) (hb : b ≤ 1) (hn1 : n = 1 → e = 0) (hr : r ≤ 2)
    (hA : 3 ≤ r + e + b) (hg : 5 * n ≤ r + e + b + 2) : n = 1 ∧ b = 1 := by
  have hn1' : n = 1 := by omega
  have he0 := hn1 hn1'
  subst hn1'
  omega

end CFSG.LocalAnalysis.GLTheoremA

end
