module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar

open Finset
open scoped Nat

theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' (Nat.two_dvd_mul_sub_one n)

theorem choose_le_choose_of_le_half {n j k : ℕ} (hjk : j ≤ k) (hk : k ≤ n / 2) :
    n.choose j ≤ n.choose k := by
  revert hk
  induction k, hjk using Nat.le_induction with
  | base =>
      intro _
      rfl
  | succ k _ ih =>
      intro hk
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem choose_one_le_choose {n k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n - 1) :
    n.choose 1 ≤ n.choose k := by
  have hk : k ≤ n := by omega
  by_cases h : k ≤ n / 2
  · exact choose_le_choose_of_le_half h1 h
  · have h' : n - k ≤ n / 2 := by omega
    rw [← Nat.choose_symm hk]
    exact choose_le_choose_of_le_half (by omega) h'

theorem le_choose {n k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n - 1) : n ≤ n.choose k := by
  simpa [Nat.choose_one_right] using choose_one_le_choose h1 h2

theorem choose_two_le_choose {n k : ℕ} (h2 : 2 ≤ k) (hk : k ≤ n - 2) :
    n.choose 2 ≤ n.choose k := by
  have hkn : k ≤ n := by omega
  by_cases h : k ≤ n / 2
  · exact choose_le_choose_of_le_half h2 h
  · have h' : n - k ≤ n / 2 := by omega
    rw [← Nat.choose_symm hkn]
    exact choose_le_choose_of_le_half (by omega) h'

theorem factorial_mul_factorial_le_pred {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (a)! * (b)! ≤ (a + b - 1)! := by
  set n := a + b with hn
  have han : a ≤ n - 1 := by omega
  have hna : n - a = b := by omega
  have hfac : (n)! = n * (n - 1)! := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [Nat.factorial_succ, Nat.sub_add_cancel (show 1 ≤ n by omega)]
  have hchoose : n ≤ n.choose a := le_choose (by omega) han
  have hspec := Nat.choose_mul_factorial_mul_factorial (show a ≤ n by omega)
  have hmul : n * ((a)! * (n - a)!) ≤ (n)! := by
    calc n * ((a)! * (n - a)!)
        ≤ n.choose a * ((a)! * (n - a)!) := Nat.mul_le_mul_right _ hchoose
      _ = n.choose a * (a)! * (n - a)! := by ring
      _ = (n)! := hspec
  rw [hna, hfac] at hmul
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

theorem factorial_mul_factorial_le_two {n x : ℕ} (hx2 : 2 ≤ x) (hxn : x ≤ n - 1) :
    (x)! * (n + 1 - x)! ≤ 2 * (n - 1)! := by
  have hxn' : x ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hfac1 : (n + 1 - x)! = (n + 1 - x) * (n - x)! := by
    rw [show n + 1 - x = (n - x) + 1 by omega, Nat.factorial_succ]
  have hkey : n * (n + 1 - x) ≤ 2 * n.choose x := by
    by_cases hx : x ≤ n - 2
    · have hc := choose_two_le_choose hx2 hx
      have hc2 := two_mul_choose_two n
      have hle : n * (n + 1 - x) ≤ n * (n - 1) :=
        Nat.mul_le_mul_left n (by omega)
      calc n * (n + 1 - x) ≤ n * (n - 1) := hle
        _ = 2 * n.choose 2 := hc2.symm
        _ ≤ 2 * n.choose x := Nat.mul_le_mul_left 2 hc
    · have hxeq : x = n - 1 := by omega
      have h1 : n + 1 - (n - 1) = 2 := by omega
      rw [hxeq, h1]
      rw [Nat.choose_symm (k := 1) (by omega), Nat.choose_one_right]
      omega
  have hspec := Nat.choose_mul_factorial_mul_factorial hxn'
  have hmul := Nat.mul_le_mul_right ((x)! * (n - x)!) hkey
  have hspec' : n.choose x * ((x)! * (n - x)!) = (n)! := by
    rw [← hspec]
    ring
  have hR : (2 * n.choose x) * ((x)! * (n - x)!) = 2 * (n)! := by
    rw [mul_assoc, hspec']
  rw [hR] at hmul
  have hfacn : (n)! = n * (n - 1)! := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [Nat.factorial_succ, Nat.sub_add_cancel (show 1 ≤ n by omega)]
  rw [hfacn] at hmul
  rw [hfac1]
  have hmul' : n * ((x)! * ((n + 1 - x) * (n - x)!)) ≤ n * (2 * (n - 1)!) := by
    calc n * ((x)! * ((n + 1 - x) * (n - x)!))
        = (n * (n + 1 - x)) * ((x)! * (n - x)!) := by ring
      _ ≤ 2 * (n * (n - 1)!) := hmul
      _ = n * (2 * (n - 1)!) := by ring
  exact Nat.le_of_mul_le_mul_left hmul' (by omega)

theorem sq_add_succ_sq_le {a d l : ℕ} (ha : 1 ≤ a) (hl : 1 ≤ l) :
    a ^ 2 + ((d + 1) ^ 2 + (l - 1)) ≤ (a + d) ^ 2 + l := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hda : d ≤ d * a := by simpa using Nat.mul_le_mul_left d ha
  nlinarith [hda]

theorem sum_sq_le {l m : ℕ} (b : Fin l → ℕ) (hb : ∀ i, 0 < b i)
    (hsum : ∑ i, b i = m) :
    ∑ i, b i ^ 2 ≤ (m - l + 1) ^ 2 + (l - 1) := by
  induction l generalizing m with
  | zero =>
      have hm : m = 0 := by simpa using hsum.symm
      subst m
      simp
  | succ l ih =>
      by_cases hl0 : l = 0
      · subst l
        have hb0 : b 0 = m := by simpa using hsum
        have hm1 : 1 ≤ m := by
          have := hb 0
          omega
        have hsq : ∑ i : Fin 1, b i ^ 2 = (b 0) ^ 2 := by simp
        rw [hsq, hb0, Nat.sub_add_cancel hm1]
        norm_num
      · set a := b 0 with ha
        set c : Fin l → ℕ := fun i => b i.succ with hc
        have hcpos : ∀ i, 0 < c i := fun i => hb i.succ
        have hsplit : a + ∑ i, c i = m := by
          simpa [a, c, Fin.sum_univ_succ] using hsum
        have hsumc : ∑ i, c i = m - a := by omega
        have hc_le : l ≤ ∑ i, c i := by
          calc l = ∑ _i : Fin l, 1 := by simp
            _ ≤ ∑ i, c i := Finset.sum_le_sum fun i _ => hcpos i
        have hih := ih c hcpos hsumc
        have hsq : ∑ i : Fin (l + 1), b i ^ 2 = a ^ 2 + ∑ i : Fin l, c i ^ 2 := by
          rw [Fin.sum_univ_succ]
        rw [hsq]
        have ha_pos : 0 < a := by simpa [a] using hb 0
        have hm_ge : l + 1 ≤ m := by omega
        have hmain : a ^ 2 + (((m - a) - l + 1) ^ 2 + (l - 1)) ≤
            (m - (l + 1) + 1) ^ 2 + l := by
          set N := m - l with hNdef
          have hN : m - (l + 1) + 1 = N := by omega
          have haN : a ≤ N := by omega
          have harg : (m - a) - l + 1 = N + 1 - a := by omega
          rw [hN, harg]
          set d := N - a with hd
          have hNa : N = a + d := by omega
          rw [hNa]
          have harg2 : a + d + 1 - a = d + 1 := by omega
          rw [harg2]
          exact sq_add_succ_sq_le (by omega) (by omega)
        calc a ^ 2 + ∑ i : Fin l, c i ^ 2
            ≤ a ^ 2 + (((m - a) - l + 1) ^ 2 + (l - 1)) := by gcongr
          _ ≤ (m - (l + 1) + 1) ^ 2 + l := hmain

theorem sum_sq_le_three {l m : ℕ} (b : Fin l → ℕ) (hb : ∀ i, 0 < b i)
    (hsum : ∑ i, b i = m) (hl : 3 ≤ l) :
    ∑ i, b i ^ 2 ≤ (m - 2) ^ 2 + 2 := by
  have hl_le_m : l ≤ m := by
    calc l = ∑ _i : Fin l, 1 := by simp
      _ ≤ ∑ i, b i := Finset.sum_le_sum fun i _ => hb i
      _ = m := hsum
  have h := sum_sq_le b hb hsum
  set n := m - 2 with hn
  set d := l - 3 with hd
  have hd_le : d ≤ n - 1 := by omega
  have h1 : m - l + 1 = n - d := by omega
  have h2 : l - 1 = d + 2 := by omega
  rw [h1, h2] at h
  set e := n - d with he
  have hn_eq : n = d + e := by omega
  nlinarith [hn_eq]

theorem sum_sq_three_le_aux {n x y z : ℕ} (hx2 : 2 ≤ x) (hxn : x ≤ n)
    (hy : 1 ≤ y) (hz : 1 ≤ z) (hsum : x + y + z = n + 3) :
    x ^ 2 + y ^ 2 + z ^ 2 ≤ n ^ 2 + 5 := by
  have hyz : y + z ≤ y * z + 1 := by
    obtain ⟨u, rfl⟩ : ∃ u, y = u + 1 := ⟨y - 1, by omega⟩
    obtain ⟨v, rfl⟩ : ∃ v, z = v + 1 := ⟨z - 1, by omega⟩
    nlinarith [Nat.zero_le (u * v)]
  have ht : y + z = n + 3 - x := by omega
  set a := x - 2 with ha
  set c := n - x with hc
  have hxeq : x = a + 2 := by omega
  have hneq : n = a + c + 2 := by omega
  have hteq : y + z = c + 3 := by omega
  have hP : 3 * n + 2 ≤ x * y + x * z + y * z := by
    have h1 : (x + 1) * (y + z) ≤ x * y + x * z + y * z + 1 := by
      nlinarith [hyz]
    nlinarith [h1, hxeq, hneq, hteq, Nat.zero_le (a * c)]
  have hsqid : (n + 3) ^ 2 = (x ^ 2 + y ^ 2 + z ^ 2) +
      2 * (x * y + x * z + y * z) := by
    calc (n + 3) ^ 2 = (x + y + z) ^ 2 := by rw [hsum]
      _ = (x ^ 2 + y ^ 2 + z ^ 2) + 2 * (x * y + x * z + y * z) := by ring
  have hsum2 : (n + 3) ^ 2 = (n ^ 2 + 5) + 2 * (3 * n + 2) := by ring
  omega

theorem sum_sq_le_of_ne {l m : ℕ} (b : Fin l → ℕ) (hb : ∀ i, 0 < b i)
    (hsum : ∑ i, b i = m) (hl : 3 ≤ l) (hm : 5 ≤ m)
    (hne : ¬ (l = 3 ∧ ∃ i, b i = m - 2)) :
    ∑ i, b i ^ 2 ≤ (m - 3) ^ 2 + 5 := by
  by_cases hl3 : l = 3
  · subst l
    have h0 := hb 0
    have h1 := hb 1
    have h2 := hb 2
    have hs : b 0 + b 1 + b 2 = m := by
      simpa [Fin.sum_univ_three] using hsum
    have hne' : ∀ i : Fin 3, b i ≠ m - 2 := by
      intro i hi
      exact hne ⟨rfl, ⟨i, hi⟩⟩
    have hle0 : b 0 ≤ m - 3 := by
      have := hne' 0
      omega
    have hle1 : b 1 ≤ m - 3 := by
      have := hne' 1
      omega
    have hle2 : b 2 ≤ m - 3 := by
      have := hne' 2
      omega
    have hsq : ∑ i : Fin 3, b i ^ 2 = b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 := by
      rw [Fin.sum_univ_three]
    rw [hsq]
    set n := m - 3 with hn
    have hm_eq : m = n + 3 := by omega
    have hle0' : b 0 ≤ n := by omega
    have hle1' : b 1 ≤ n := by omega
    have hle2' : b 2 ≤ n := by omega
    have hs' : b 0 + b 1 + b 2 = n + 3 := by omega
    have hn2 : 2 ≤ n := by omega
    by_cases h0 : 2 ≤ b 0
    · have := sum_sq_three_le_aux (n := n) (x := b 0) (y := b 1) (z := b 2)
        h0 hle0' (by omega) (by omega) (by omega)
      simpa [add_assoc] using this
    · have hb0 : b 0 = 1 := by omega
      by_cases h1 : 2 ≤ b 1
      · have := sum_sq_three_le_aux (n := n) (x := b 1) (y := b 0) (z := b 2)
          h1 hle1' (by omega) (by omega) (by omega)
        simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using this
      · have hb1 : b 1 = 1 := by omega
        have h2 : 2 ≤ b 2 := by omega
        have := sum_sq_three_le_aux (n := n) (x := b 2) (y := b 0) (z := b 1)
          h2 hle2' (by omega) (by omega) (by omega)
        simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using this
  · have hl4 : 4 ≤ l := by omega
    have hl_le_m : l ≤ m := by
      calc l = ∑ _i : Fin l, 1 := by simp
        _ ≤ ∑ i, b i := Finset.sum_le_sum fun i _ => hb i
        _ = m := hsum
    have h := sum_sq_le b hb hsum
    set n := m - 3 with hn
    set d := l - 4 with hd
    have hd_le : d ≤ n - 1 := by omega
    have h1 : m - l + 1 = n - d := by omega
    have h2 : l - 1 = d + 3 := by omega
    rw [h1, h2] at h
    set e := n - d with he
    have hn_eq : n = d + e := by omega
    nlinarith [hn_eq]

theorem prod_factorial_le {l m : ℕ} (b : Fin l → ℕ) (hb : ∀ i, 0 < b i)
    (hsum : ∑ i, b i = m) :
    (∏ i, (b i)!) ≤ (m - l + 1)! := by
  induction l generalizing m with
  | zero =>
      have hm : m = 0 := by simpa using hsum.symm
      subst m
      simp
  | succ l ih =>
      set a := b 0 with ha
      set c : Fin l → ℕ := fun i => b i.succ with hc
      have hcpos : ∀ i, 0 < c i := fun i => hb i.succ
      have hsplit : a + ∑ i, c i = m := by
        simpa [a, c, Fin.sum_univ_succ] using hsum
      have hsumc : ∑ i, c i = m - a := by omega
      have hprod : (∏ i : Fin (l + 1), (b i)!) = (a)! * ∏ i : Fin l, (c i)! := by
        rw [Fin.prod_univ_succ]
      rw [hprod]
      have hih := ih c hcpos hsumc
      set N := m - l with hNdef
      have ha_le : a ≤ N := by
        have hc_le : l ≤ ∑ i, c i := by
          calc l = ∑ _i : Fin l, 1 := by simp
            _ ≤ ∑ i, c i := Finset.sum_le_sum fun i _ => hcpos i
        omega
      have ha_pos : 0 < a := by simpa [a] using hb 0
      have hm_ge : l + 1 ≤ m := by omega
      have harg1 : (m - a) - l + 1 = N + 1 - a := by omega
      have harg2 : m - (l + 1) + 1 = N := by omega
      rw [harg2]
      refine (Nat.mul_le_mul_left _ hih).trans ?_
      rw [harg1]
      have hN_succ : 1 ≤ N + 1 - a := by omega
      have hfac := factorial_mul_factorial_le_pred (a := a) (b := N + 1 - a)
        ha_pos hN_succ
      have harg3 : a + (N + 1 - a) - 1 = N := by omega
      rwa [harg3] at hfac

theorem multinomial_lower {l m : ℕ} (b : Fin l → ℕ) (hb : ∀ i, 0 < b i)
    (hsum : ∑ i, b i = m) (hl : 3 ≤ l) :
    m * (m - 1) ≤ Nat.multinomial Finset.univ b := by
  have hl_le_m : l ≤ m := by
    calc l = ∑ _i : Fin l, 1 := by simp
      _ ≤ ∑ i, b i := Finset.sum_le_sum fun i _ => hb i
      _ = m := hsum
  have hm2 : 2 ≤ m := by omega
  have hprod := prod_factorial_le b hb hsum
  have hle : m - l + 1 ≤ m - 2 := by omega
  have hprod2 : (∏ i, (b i)!) ≤ (m - 2)! := hprod.trans (Nat.factorial_le hle)
  have hspec := Nat.multinomial_spec (s := Finset.univ) (f := b)
  rw [hsum] at hspec
  have hfac : (m)! = (m * (m - 1)) * (m - 2)! := by
    have hdesc : m.descFactorial 2 = m * (m - 1) := by
      simp [Nat.descFactorial]
      ring
    rw [← Nat.factorial_mul_descFactorial (show 2 ≤ m by omega), hdesc]
    ring
  have hspec' : (∏ i, (b i)!) * Nat.multinomial Finset.univ b =
      (m * (m - 1)) * (m - 2)! := by
    rw [hspec, hfac]
  have h : (m - 2)! * (m * (m - 1)) ≤ (m - 2)! * Nat.multinomial Finset.univ b := by
    rw [mul_comm (m - 2)! (m * (m - 1)), ← hspec']
    exact Nat.mul_le_mul_right _ hprod2
  exact Nat.le_of_mul_le_mul_left h (Nat.factorial_pos (m - 2))

theorem factorial_three_le_two {m x y z : ℕ} (hx2 : 2 ≤ x) (hx3 : x ≤ m - 3)
    (hy : 0 < y) (hz : 0 < z) (hsum : x + y + z = m) :
    (x)! * (y)! * (z)! ≤ 2 * (m - 3)! := by
  have hyz : (y)! * (z)! ≤ (y + z - 1)! :=
    factorial_mul_factorial_le_pred (by omega) (by omega)
  have hyz_eq : y + z - 1 = m - x - 1 := by omega
  have hxrange : x ≤ (m - 2) - 1 := by omega
  have htwo := factorial_mul_factorial_le_two (n := m - 2) (x := x) hx2 hxrange
  have harg1 : (m - 2) + 1 - x = m - x - 1 := by omega
  have harg2 : (m - 2) - 1 = m - 3 := by omega
  rw [harg1, harg2] at htwo
  calc (x)! * (y)! * (z)! = (x)! * ((y)! * (z)!) := by ring
    _ ≤ (x)! * (y + z - 1)! := Nat.mul_le_mul_left _ hyz
    _ = (x)! * (m - x - 1)! := by rw [hyz_eq]
    _ ≤ 2 * (m - 3)! := htwo

theorem prod_factorial_three_le_two {m : ℕ} (b : Fin 3 → ℕ) (hb : ∀ i, 0 < b i)
    (hsum : ∑ i, b i = m) (hne : ¬ ∃ i, b i = m - 2) :
    (∏ i, (b i)!) ≤ 2 * (m - 3)! := by
  have hb0pos : 0 < b 0 := hb 0
  have hb1pos : 0 < b 1 := hb 1
  have hb2pos : 0 < b 2 := hb 2
  have hs : b 0 + b 1 + b 2 = m := by
    simpa [Fin.sum_univ_three] using hsum
  have hprod : (∏ i : Fin 3, (b i)!) = (b 0)! * (b 1)! * (b 2)! := by
    rw [Fin.prod_univ_three]
  rw [hprod]
  by_cases h0 : 2 ≤ b 0
  · have h03 : b 0 ≤ m - 3 := by
      have hne0 : b 0 ≠ m - 2 := fun h => hne ⟨0, h⟩
      have hle : b 0 ≤ m - 2 := by omega
      have hlt : b 0 < m - 2 := lt_of_le_of_ne hle hne0
      omega
    have h := factorial_three_le_two (m := m) (x := b 0) (y := b 1) (z := b 2)
      h0 h03 (hb 1) (hb 2) (by omega)
    simpa [mul_assoc] using h
  · have hb0 : b 0 = 1 := by have := hb 0; omega
    by_cases h1 : 2 ≤ b 1
    · have h13 : b 1 ≤ m - 3 := by
        have hne1 : b 1 ≠ m - 2 := fun h => hne ⟨1, h⟩
        have hle : b 1 ≤ m - 2 := by omega
        have hlt : b 1 < m - 2 := lt_of_le_of_ne hle hne1
        omega
      have h := factorial_three_le_two (m := m) (x := b 1) (y := b 0) (z := b 2)
        h1 h13 (hb 0) (hb 2) (by omega)
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    · have hb1 : b 1 = 1 := by have := hb 1; omega
      have h2eq : b 2 = m - 2 := by omega
      exact False.elim (hne ⟨2, h2eq⟩)

theorem multinomial_lower_ne {l m : ℕ} (b : Fin l → ℕ) (hb : ∀ i, 0 < b i)
    (hsum : ∑ i, b i = m) (hl : 3 ≤ l) (hm : 5 ≤ m)
    (hne : ¬ (l = 3 ∧ ∃ i, b i = m - 2)) :
    m * (m - 1) * (m - 2) ≤ 2 * Nat.multinomial Finset.univ b := by
  have hl_le_m : l ≤ m := by
    calc l = ∑ _i : Fin l, 1 := by simp
      _ ≤ ∑ i, b i := Finset.sum_le_sum fun i _ => hb i
      _ = m := hsum
  have hspec := Nat.multinomial_spec (s := Finset.univ) (f := b)
  rw [hsum] at hspec
  have hfac : (m)! = (m * (m - 1) * (m - 2)) * (m - 3)! := by
    have hdesc : m.descFactorial 3 = m * (m - 1) * (m - 2) := by
      simp [Nat.descFactorial]
      ring
    rw [← Nat.factorial_mul_descFactorial (show 3 ≤ m by omega), hdesc]
    ring
  have hprod : (∏ i, (b i)!) ≤ 2 * (m - 3)! := by
    by_cases hl3 : l = 3
    · subst l
      have hne' : ¬ ∃ i, b i = m - 2 := fun h => hne ⟨rfl, h⟩
      exact prod_factorial_three_le_two b hb hsum hne'
    · have hl4 : 4 ≤ l := by omega
      have h := prod_factorial_le b hb hsum
      have hle : m - l + 1 ≤ m - 3 := by omega
      have h1 : (∏ i, (b i)!) ≤ (m - 3)! := h.trans (Nat.factorial_le hle)
      have h2 : (m - 3)! ≤ 2 * (m - 3)! := by
        have := Nat.factorial_pos (m - 3)
        omega
      exact h1.trans h2
  have hspec' : (∏ i, (b i)!) * Nat.multinomial Finset.univ b =
      (m * (m - 1) * (m - 2)) * (m - 3)! := by
    rw [hspec, hfac]
  have h : (m - 3)! * (m * (m - 1) * (m - 2)) ≤
      (m - 3)! * (2 * Nat.multinomial Finset.univ b) := by
    rw [mul_comm (m - 3)! (m * (m - 1) * (m - 2)), ← hspec']
    calc (∏ i, (b i)!) * Nat.multinomial Finset.univ b
        ≤ (2 * (m - 3)!) * Nat.multinomial Finset.univ b :=
          Nat.mul_le_mul_right _ hprod
      _ = (m - 3)! * (2 * Nat.multinomial Finset.univ b) := by ring
  exact Nat.le_of_mul_le_mul_left h (Nat.factorial_pos (m - 3))

theorem mul_sq_add_four_lt_pow {m t : ℕ} (hm : 5 ≤ m) (ht : 3 ≤ t) :
    t * (m ^ 2 + 4) < 4 * m ^ (t - 1) := by
  induction t, ht using Nat.le_induction with
  | base =>
      norm_num
      nlinarith
  | succ k _ ih =>
      have hstep : k + 1 ≤ m * k := by nlinarith
      have hk1 : 1 ≤ k := by omega
      calc (k + 1) * (m ^ 2 + 4)
          ≤ (m * k) * (m ^ 2 + 4) := Nat.mul_le_mul_right _ hstep
        _ = m * (k * (m ^ 2 + 4)) := by ring
        _ < m * (4 * m ^ (k - 1)) :=
            Nat.mul_lt_mul_of_pos_left ih (by omega)
        _ = 4 * m ^ k := by
            have hpow : m * m ^ (k - 1) = m ^ k := by
              rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hk1]
            calc m * (4 * m ^ (k - 1)) = 4 * (m * m ^ (k - 1)) := by ring
              _ = 4 * m ^ k := by rw [hpow]

theorem sq_add_four_lt_choose_add_sq {m : ℕ} (hm : 5 ≤ m) :
    m ^ 2 + 4 < 2 * (m.choose 2 + (m - 2) ^ 2) := by
  set k := m - 2 with hk
  have hmk : m = k + 2 := by omega
  have hc := two_mul_choose_two m
  rw [hmk] at hc ⊢
  norm_num at hc ⊢
  nlinarith

theorem mul_le_two_mul_choose {m j : ℕ} (hj : 3 ≤ j) (hjm : j + 3 ≤ m) :
    (m - 2) * (m - 3) ≤ 2 * (m - 2).choose (j - 1) := by
  have h2 : 2 ≤ j - 1 := by omega
  have hle : j - 1 ≤ (m - 2) - 2 := by omega
  have hc := choose_two_le_choose h2 hle
  have hc2 := two_mul_choose_two (m - 2)
  have hsub : (m - 2) - 1 = m - 3 := by omega
  rw [hsub] at hc2
  calc (m - 2) * (m - 3) = 2 * (m - 2).choose 2 := hc2.symm
    _ ≤ 2 * (m - 2).choose (j - 1) := Nat.mul_le_mul_left 2 hc

theorem sq_add_four_lt_four_mul {m : ℕ} (hm : 6 ≤ m) :
    m ^ 2 + 4 < 4 * ((m - 2) * (m - 3)) := by
  set j := m - 6 with hj
  have hmj : m = j + 6 := by omega
  rw [hmj]
  norm_num
  nlinarith

theorem choose_three_le_choose_half {m : ℕ} (hm : 8 ≤ m) (_he : Even m) :
    (m - 2).choose 3 ≤ (m - 2).choose (m / 2 - 1) := by
  have hmid : m / 2 - 1 = (m - 2) / 2 := by omega
  rw [hmid]
  exact Nat.choose_le_middle 3 (m - 2)

theorem sq_add_four_lt_four_mul_choose_three {m : ℕ} (hm : 8 ≤ m) :
    m ^ 2 + 4 < 4 * (m - 2).choose 3 := by
  set j := m - 8 with hj
  have hmj : m = j + 8 := by omega
  set n := m - 2 with hn
  have hmn : m = n + 2 := by omega
  have hn6 : 6 ≤ n := by omega
  have hspec : n.choose 3 * 6 * (n - 3)! = (n)! := by
    have h := Nat.choose_mul_factorial_mul_factorial (show 3 ≤ n by omega)
    norm_num [Nat.factorial] at h
    simpa using h
  have hfacn : (n)! = n * (n - 1) * (n - 2) * (n - 3)! := by
    have hdesc : n.descFactorial 3 = n * (n - 1) * (n - 2) := by
      simp [Nat.descFactorial]
      ring
    rw [← Nat.factorial_mul_descFactorial (show 3 ≤ n by omega), hdesc]
    ring
  have hfac : 6 * n.choose 3 = n * (n - 1) * (n - 2) := by
    apply Nat.mul_left_cancel (Nat.factorial_pos (n - 3))
    calc (n - 3)! * (6 * n.choose 3)
        = n.choose 3 * 6 * (n - 3)! := by ring
      _ = (n)! := hspec
      _ = n * (n - 1) * (n - 2) * (n - 3)! := hfacn
      _ = (n - 3)! * (n * (n - 1) * (n - 2)) := by ring
  rw [hmj]
  have hn_eq : n = j + 6 := by omega
  rw [hn_eq]
  have hfac' : 6 * (j + 6).choose 3 = (j + 6) * (j + 5) * (j + 4) := by
    rw [hn_eq] at hfac
    have h1 : j + 6 - 1 = j + 5 := by omega
    have h2 : j + 6 - 2 = j + 4 := by omega
    rw [h1, h2] at hfac
    exact hfac
  have h3 : 6 * ((j + 8) ^ 2 + 4) < 6 * (4 * (j + 6).choose 3) := by
    have h4 : 4 * ((j + 6) * (j + 5) * (j + 4)) = 6 * (4 * (j + 6).choose 3) := by
      nlinarith [hfac']
    rw [← h4]
    have hM : 0 < 4 * j ^ 3 + 54 * j ^ 2 + 200 * j + 72 := by positivity
    have hdiff : 6 * ((j + 8) ^ 2 + 4) + (4 * j ^ 3 + 54 * j ^ 2 + 200 * j + 72) =
        4 * ((j + 6) * (j + 5) * (j + 4)) := by ring
    omega
  omega

theorem sq_add_four_lt_two_mul {m : ℕ} (hm : 5 ≤ m) :
    m ^ 2 + 4 < 2 * ((m - 2) * (3 * m - 7)) := by
  set j := m - 5 with hj
  have hmj : m = j + 5 := by omega
  rw [hmj]
  norm_num
  have h3 : 3 * (j + 5) - 7 = 3 * j + 8 := by omega
  rw [h3]
  nlinarith

theorem sq_add_four_lt_four_mul_choose_two {m : ℕ} (hm : 4 ≤ m) :
    m ^ 2 + 4 < 4 * m.choose 2 := by
  set j := m - 4 with hj
  have hmj : m = j + 4 := by omega
  have hc := two_mul_choose_two m
  rw [hmj] at hc ⊢
  norm_num at hc ⊢
  nlinarith

theorem two_mul_mul_add_multinomial_le {l m : ℕ} (b : Fin l → ℕ) (hb : ∀ i, 0 < b i)
    (hsum : ∑ i, b i = m) (hl : 3 ≤ l) :
    2 * m * (m - 1) * (2 * m - 3) + Nat.multinomial Finset.univ b * ∑ i, b i ^ 2 ≤
      Nat.multinomial Finset.univ b * m ^ 2 := by
  have hl_le_m : l ≤ m := by
    calc l = ∑ _i : Fin l, 1 := by simp
      _ ≤ ∑ i, b i := Finset.sum_le_sum fun i _ => hb i
      _ = m := hsum
  have hT := sum_sq_le_three b hb hsum hl
  have hN := multinomial_lower b hb hsum hl
  have hT' : (∑ i, b i ^ 2) + (4 * m - 6) ≤ m ^ 2 := by
    have hcalc : ((m - 2) ^ 2 + 2) + (4 * m - 6) = m ^ 2 := by
      set k := m - 2 with hk
      have hmk : m = k + 2 := by omega
      rw [hmk]
      have hsub : 4 * (k + 2) - 6 = 4 * k + 2 := by omega
      rw [hsub]
      ring
    omega
  have hA : 2 * m * (m - 1) * (2 * m - 3) ≤
      Nat.multinomial Finset.univ b * (4 * m - 6) := by
    have hmul := Nat.mul_le_mul_right (4 * m - 6) hN
    have harith : m * (m - 1) * (4 * m - 6) = 2 * m * (m - 1) * (2 * m - 3) := by
      have h1 : 4 * m - 6 = 2 * (2 * m - 3) := by omega
      rw [h1]
      ring
    rwa [harith] at hmul
  calc 2 * m * (m - 1) * (2 * m - 3) + Nat.multinomial Finset.univ b * ∑ i, b i ^ 2
      ≤ Nat.multinomial Finset.univ b * (4 * m - 6) +
          Nat.multinomial Finset.univ b * ∑ i, b i ^ 2 := add_le_add_left hA _
    _ = Nat.multinomial Finset.univ b * ∑ i, b i ^ 2 +
          Nat.multinomial Finset.univ b * (4 * m - 6) := by ring
    _ = Nat.multinomial Finset.univ b * ((∑ i, b i ^ 2) + (4 * m - 6)) := by ring
    _ ≤ Nat.multinomial Finset.univ b * m ^ 2 := Nat.mul_le_mul_left _ hT'

theorem mul_add_multinomial_le_of_ne {l m : ℕ} (b : Fin l → ℕ) (hb : ∀ i, 0 < b i)
    (hsum : ∑ i, b i = m) (hl : 3 ≤ l) (hm : 5 ≤ m)
    (hne : ¬ (l = 3 ∧ ∃ i, b i = m - 2)) :
    m * (m - 1) * (m - 2) * (3 * m - 7) + Nat.multinomial Finset.univ b * ∑ i, b i ^ 2 ≤
      Nat.multinomial Finset.univ b * m ^ 2 := by
  have hT := sum_sq_le_of_ne b hb hsum hl hm hne
  have hN := multinomial_lower_ne b hb hsum hl hm hne
  have hT' : (∑ i, b i ^ 2) + (6 * m - 14) ≤ m ^ 2 := by
    have hcalc : ((m - 3) ^ 2 + 5) + (6 * m - 14) = m ^ 2 := by
      set k := m - 3 with hk
      have hmk : m = k + 3 := by omega
      rw [hmk]
      have hsub : 6 * (k + 3) - 14 = 6 * k + 4 := by omega
      rw [hsub]
      ring
    omega
  have hA : m * (m - 1) * (m - 2) * (3 * m - 7) ≤
      Nat.multinomial Finset.univ b * (6 * m - 14) := by
    have hmul := Nat.mul_le_mul_right (3 * m - 7) hN
    have hright : (2 * Nat.multinomial Finset.univ b) * (3 * m - 7) =
        Nat.multinomial Finset.univ b * (6 * m - 14) := by
      have h2 : 6 * m - 14 = 2 * (3 * m - 7) := by omega
      rw [h2]
      ring
    rwa [hright] at hmul
  calc m * (m - 1) * (m - 2) * (3 * m - 7) +
        Nat.multinomial Finset.univ b * ∑ i, b i ^ 2
      ≤ Nat.multinomial Finset.univ b * (6 * m - 14) +
          Nat.multinomial Finset.univ b * ∑ i, b i ^ 2 := add_le_add_left hA _
    _ = Nat.multinomial Finset.univ b * ∑ i, b i ^ 2 +
          Nat.multinomial Finset.univ b * (6 * m - 14) := by ring
    _ = Nat.multinomial Finset.univ b * ((∑ i, b i ^ 2) + (6 * m - 14)) := by ring
    _ ≤ Nat.multinomial Finset.univ b * m ^ 2 := Nat.mul_le_mul_left _ hT'

end CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
