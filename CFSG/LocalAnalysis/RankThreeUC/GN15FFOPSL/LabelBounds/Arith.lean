module

public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL

open Finset CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar CFSG.LieType.SpecialLinear.ExteriorModel

theorem lt_mul_sq_of_period {f s d h n : ℕ} (hs : f ≤ s * h) (hdim : s * d < f * n ^ 2) :
    d < h * n ^ 2 := by
  have h : s * d < s * (h * n ^ 2) := by
    calc s * d < f * n ^ 2 := hdim
      _ ≤ s * h * n ^ 2 := Nat.mul_le_mul_right _ hs
      _ = s * (h * n ^ 2) := by ring
  exact Nat.lt_of_mul_lt_mul_left h

theorem mul_sq_lt_pow_of_three_le {n h : ℕ} (hn : 5 ≤ n) (hh : 3 ≤ h) : h * n ^ 2 < n ^ h := by
  have h4 := mul_sq_add_four_lt_pow (m := n) (t := h) hn hh
  have h1 : h * n ^ 2 < h * (n ^ 2 + 4) :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  have h2 : 4 * n ^ (h - 1) ≤ n * n ^ (h - 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : n * n ^ (h - 1) = n ^ h := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega)]
  calc h * n ^ 2 < h * (n ^ 2 + 4) := h1
    _ < 4 * n ^ (h - 1) := h4
    _ ≤ n * n ^ (h - 1) := h2
    _ = n ^ h := h3

theorem two_mul_sq_le_mul_choose_two {n : ℕ} (hn : 5 ≤ n) : 2 * n ^ 2 ≤ n * n.choose 2 := by
  have hc := two_mul_choose_two n
  set m := n - 5 with hm
  have hn' : n = m + 5 := by omega
  have hsub : m + 5 - 1 = m + 4 := by omega
  rw [hn'] at hc ⊢
  rw [hsub] at hc
  nlinarith

theorem sq_le_mul_pred_add_choose_three {n : ℕ} (hn : 4 ≤ n) :
    n ^ 2 ≤ n * (n - 1) + n.choose 3 := by
  have hle : n ≤ n.choose 3 := le_choose (by norm_num) (by omega)
  set m := n - 4 with hm
  have hn' : n = m + 4 := by omega
  have hsub : m + 4 - 1 = m + 3 := by omega
  rw [hn'] at hle ⊢
  rw [hsub]
  nlinarith

theorem six_mul_choose_three (n : ℕ) : 6 * n.choose 3 = n * (n - 1) * (n - 2) := by
  have h1 := Nat.descFactorial_eq_factorial_mul_choose n 3
  have hf : Nat.factorial 3 = 6 := by decide
  rw [hf] at h1
  have h2 : n.descFactorial 3 = n * (n - 1) * (n - 2) := by
    simp [Nat.descFactorial]
    ring
  exact h1.symm.trans h2

theorem eq_six_three_of_choose_lt_sq {n j r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrn : r ∣ n)
    (hrj : r ∣ j) (hj : 0 < j) (hjn : j < n) (hlt : n.choose j < n ^ 2) : n = 6 ∧ j = 3 := by
  have hr3 : 3 ≤ r := by
    have h2 := hr.two_le
    omega
  have hrn0 : 0 < n := by omega
  have hrn' : r ≤ n := Nat.le_of_dvd hrn0 hrn
  have hj3 : 3 ≤ j := by
    have h := Nat.le_of_dvd hj hrj
    omega
  have hnj : j ≤ n := by omega
  have hdvd : r ∣ n - j := Nat.dvd_sub hrn hrj
  have h3nj : 3 ≤ n - j := by
    have hpos : 0 < n - j := by omega
    have h := Nat.le_of_dvd hpos hdvd
    omega
  have hn6 : 6 ≤ n := by omega
  by_cases hn9 : 9 ≤ n
  · have hchoose : n.choose 3 ≤ n.choose j := by
      by_cases hhalf : j ≤ n / 2
      · exact choose_le_choose_of_le_half hj3 hhalf
      · have hnj' : n - j ≤ n / 2 := by omega
        rw [← Nat.choose_symm hnj]
        exact choose_le_choose_of_le_half (by omega) hnj'
    have h3 : n ^ 2 ≤ n.choose 3 := by
      have hfac := six_mul_choose_three n
      have h6 : 6 * n ^ 2 ≤ 6 * n.choose 3 := by
        rw [hfac]
        set m := n - 9 with hm
        have hn' : n = m + 9 := by omega
        have h1 : m + 9 - 1 = m + 8 := by omega
        have h2 : m + 9 - 2 = m + 7 := by omega
        rw [hn', h1, h2]
        nlinarith
      exact Nat.le_of_mul_le_mul_left h6 (by norm_num)
    omega
  · have hn8 : n ≤ 8 := by omega
    interval_cases n
    · have hr6 : r = 3 := by
        have hle : r ≤ 6 := by omega
        interval_cases r
        · rfl
        · exact absurd hr (by decide)
        · norm_num at hrn
        · exact absurd hr (by decide)
      rw [hr6] at hrj
      have hj6 : j = 3 := by
        have hle : j ≤ 5 := by omega
        interval_cases j
        · rfl
        · norm_num at hrj
        · norm_num at hrj
      subst hj6
      exact ⟨rfl, rfl⟩
    · have hr7 : r = 7 := by
        have hle : r ≤ 7 := by omega
        interval_cases r
        · norm_num at hrn
        · exact absurd hr (by decide)
        · norm_num at hrn
        · exact absurd hr (by decide)
        · rfl
      rw [hr7] at hrj
      have hle : j ≤ 6 := by omega
      interval_cases j <;> norm_num at hrj
    · have hle : r ≤ 8 := by omega
      interval_cases r
      · norm_num at hrn
      · exact absurd hr (by decide)
      · norm_num at hrn
      · exact absurd hr (by decide)
      · norm_num at hrn
      · exact absurd hr (by decide)

theorem pow_card_active_le_prod_orbitSize {n f : ℕ} (hn : 2 ≤ n) (ε : Fin f → Finset (Fin n))
    (h0 : ∀ i, (⟨0, by omega⟩ : Fin n) ∉ ε i) :
    n ^ (univ.filter fun i => ε i ≠ ∅).card ≤
      ∏ i ∈ univ.filter (fun i => ε i ≠ ∅), orbitSize (ε i) := by
  classical
  calc n ^ (univ.filter fun i => ε i ≠ ∅).card
      = ∏ _i ∈ univ.filter (fun i => ε i ≠ ∅), n :=
        (Finset.prod_const (s := univ.filter fun i => ε i ≠ ∅) n).symm
    _ ≤ ∏ i ∈ univ.filter (fun i => ε i ≠ ∅), orbitSize (ε i) :=
        Finset.prod_le_prod' fun i hi =>
          n_le_orbitSize hn (h0 i) (Finset.mem_filter.mp hi).2

theorem sq_le_orbitSize_of_two_le_card {n : ℕ} {S : Finset (Fin n)} (hn : 5 ≤ n)
    (h0 : (⟨0, by omega⟩ : Fin n) ∉ S) (hS : 2 ≤ S.card)
    (hne : ¬ (S.card = 2 ∧ ∃ k, blocks S k = n - 2)) : n ^ 2 ≤ orbitSize S := by
  classical
  rw [orbitSize, card_rearr_topWt]
  have hn0 : 0 < n := by omega
  have hb : ∀ i, 0 < blocks S i := fun i => blocks_pos hn0 (by simpa using h0) i
  have hsum := sum_blocks S
  have hl : 3 ≤ S.card + 1 := by omega
  have hN := multinomial_lower_ne (b := blocks S) hb hsum hl hn
    (fun h => hne ⟨by omega, h.2⟩)
  have h2 : 2 * n ^ 2 ≤ n * (n - 1) * (n - 2) := by
    set m := n - 5 with hm
    have hn' : n = m + 5 := by omega
    have h1 : m + 5 - 1 = m + 4 := by omega
    have h2' : m + 5 - 2 = m + 3 := by omega
    rw [hn', h1, h2']
    nlinarith
  have h2N : 2 * n ^ 2 ≤ 2 * Nat.multinomial univ (blocks S) := h2.trans hN
  exact Nat.le_of_mul_le_mul_left h2N (by norm_num)

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL
