module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

lemma odd_sq_mod_eight {x : ℕ} (hx : Odd x) : x ^ 2 % 8 = 1 := by
  have h2 : x % 2 = 1 := Nat.odd_iff.mp hx
  have hx8 : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  rw [Nat.pow_mod]
  rcases hx8 with h | h | h | h <;> rw [h] <;> norm_num

lemma two_pow_dvd_sq_sub_one {x j : ℕ} (hx : Odd x) (h : 2 ^ (j + 3) ∣ x - 1) :
    2 ^ (j + 4) ∣ x ^ 2 - 1 := by
  have h2dvd : 2 ∣ x + 1 := by
    obtain ⟨c, hc⟩ := hx
    exact ⟨c + 1, by omega⟩
  have hprod : 2 ^ (j + 3) * 2 ∣ (x - 1) * (x + 1) := Nat.mul_dvd_mul h h2dvd
  rw [show 2 ^ (j + 3) * 2 = 2 ^ (j + 4) by rfl] at hprod
  have heq : (x - 1) * (x + 1) = x ^ 2 - 1 := by
    have hxx : x * (x + 1) = x * x + x := by ring
    rw [Nat.sub_mul, one_mul, hxx, pow_two]
    omega
  rwa [heq] at hprod

lemma two_pow_dvd_pow_two_pow_sub_one {s : ℕ} (hs : Odd s) (j : ℕ) :
    2 ^ (j + 3) ∣ s ^ 2 ^ (j + 1) - 1 := by
  induction j with
  | zero =>
      have h : s ^ 2 % 8 = 1 := odd_sq_mod_eight hs
      rw [show (2 : ℕ) ^ (0 + 3) = 8 by norm_num]
      have hd := Nat.dvd_sub_mod (n := 8) (s ^ 2)
      rwa [h] at hd
  | succ j ih =>
      have h := two_pow_dvd_sq_sub_one (x := s ^ 2 ^ (j + 1)) (hs.pow) ih
      rw [← pow_mul, show 2 ^ (j + 1) * 2 = 2 ^ (j + 2) by rfl] at h
      exact h

lemma two_pow_ne_one {n : ℕ} (hn : n ≠ 0) : (2 : ℕ) ^ n ≠ 1 := by
  have : 2 ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma mod_eq_one_of_dvd_sub_one {a n : ℕ} (hn : n ≠ 1) (h : n ∣ a - 1) (ha : 1 ≤ a) :
    a % n = 1 := by
  have h1 : a = (a - 1) + 1 := by omega
  rw [h1, Nat.add_mod, Nat.dvd_iff_mod_eq_zero.mp h, Nat.zero_add]
  simp [Nat.one_mod_eq_one, hn]

lemma geom_sum_mul_nat {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    (∑ i ∈ Finset.range n, m ^ i) * (m - 1) = m ^ n - 1 := by
  rcases eq_or_lt_of_le hm with rfl | hm2
  · simp
  · have hdiv : m - 1 ∣ m ^ n - 1 := by
      simpa using Nat.pow_sub_one_dvd_pow_sub_one m (m := 1) (k := n) (by simp)
    rw [Nat.geomSum_eq (by omega : 2 ≤ m) n, Nat.div_mul_cancel hdiv]

lemma geom_sum_double (u e : ℕ) :
    ∑ i ∈ Finset.range (2 ^ (e + 1)), u ^ i =
      (∑ i ∈ Finset.range (2 ^ e), u ^ i) * (1 + u ^ 2 ^ e) := by
  have hsum : (∑ i ∈ Finset.range (2 ^ e), u ^ (2 ^ e + i))
      = ∑ i ∈ Finset.range (2 ^ e), u ^ i * u ^ 2 ^ e := by
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_add]
    ring
  rw [show 2 ^ (e + 1) = 2 ^ e + 2 ^ e by rw [pow_succ]; ring, Finset.sum_range_add]
  rw [show (∑ i ∈ Finset.range (2 ^ e), u ^ i) * (1 + u ^ 2 ^ e)
        = (∑ i ∈ Finset.range (2 ^ e), u ^ i)
            + (∑ i ∈ Finset.range (2 ^ e), u ^ i) * u ^ 2 ^ e by ring]
  rw [Finset.sum_mul, hsum]

lemma one_add_pow_two_pow_eq_two_mul_odd {u : ℕ} (hu : Odd u) (e : ℕ) :
    ∃ b, Odd b ∧ 1 + u ^ 2 ^ (e + 1) = 2 * b := by
  have h : (u ^ 2 ^ e) ^ 2 % 8 = 1 := odd_sq_mod_eight (hu.pow)
  have hv : u ^ 2 ^ (e + 1) % 8 = 1 := by
    rw [← pow_mul, show 2 ^ e * 2 = 2 ^ (e + 1) by rfl] at h
    exact h
  have hv' : u ^ 2 ^ (e + 1) = 8 * (u ^ 2 ^ (e + 1) / 8) + 1 := by
    have := Nat.div_add_mod (u ^ 2 ^ (e + 1)) 8
    omega
  refine ⟨4 * (u ^ 2 ^ (e + 1) / 8) + 1, ⟨2 * (u ^ 2 ^ (e + 1) / 8), by ring⟩, ?_⟩
  omega

lemma geom_sum_four_dvd {u : ℕ} (hu : u % 4 = 1) (e : ℕ) :
    ∃ a, Odd a ∧ ∑ i ∈ Finset.range (2 ^ (e + 1)), u ^ i = 2 ^ (e + 1) * a := by
  have huodd : Odd u := by
    rw [Nat.odd_iff]
    calc u % 2 = u % 4 % 2 := (Nat.mod_mod_of_dvd u (by norm_num : 2 ∣ 4)).symm
      _ = 1 % 2 := by rw [hu]
      _ = 1 := by norm_num
  induction e with
  | zero =>
      set q := u / 4 with hq
      have hu' : u = 4 * q + 1 := by
        have := Nat.div_add_mod u 4
        rw [← hq] at this
        omega
      refine ⟨2 * q + 1, ⟨q, by ring⟩, ?_⟩
      have hsum : ∑ i ∈ Finset.range (2 ^ (0 + 1)), u ^ i = 1 + u := by
        norm_num [Finset.sum_range_succ]
      rw [hsum, hu']
      ring
  | succ e ih =>
      obtain ⟨a, ha, hSa⟩ := ih
      obtain ⟨b, hb, hb_eq⟩ := one_add_pow_two_pow_eq_two_mul_odd huodd e
      refine ⟨a * b, ha.mul hb, ?_⟩
      rw [geom_sum_double u (e + 1), hSa, hb_eq]
      rw [show (2 : ℕ) ^ (e + 2) = 2 ^ (e + 1) * 2 by
        rw [show e + 2 = (e + 1) + 1 by omega, pow_succ]]
      ring

lemma geom_sum_odd {w k : ℕ} (hw : Odd w) (hk : Odd k) :
    Odd (∑ i ∈ Finset.range k, w ^ i) := by
  rw [Nat.odd_iff]
  have h : ∀ k, (∑ i ∈ Finset.range k, w ^ i) % 2 = k % 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.odd_iff.mp (hw.pow (n := k))]
        omega
  rw [h k, Nat.odd_iff.mp hk]

lemma geom_sum_cross {s : ℕ} (hs : 2 ≤ s) (k e : ℕ) :
    (∑ i ∈ Finset.range (2 ^ e), (s ^ k) ^ i) * (∑ i ∈ Finset.range k, s ^ i)
      = (∑ i ∈ Finset.range (2 ^ e), s ^ i) * (∑ i ∈ Finset.range k, (s ^ 2 ^ e) ^ i) := by
  have hs1 : 0 < s - 1 := by omega
  apply Nat.mul_right_cancel (m := s - 1) hs1
  have hA : (∑ i ∈ Finset.range (2 ^ e), (s ^ k) ^ i) * (s ^ k - 1) = (s ^ k) ^ 2 ^ e - 1 :=
    geom_sum_mul_nat (Nat.one_le_pow k s (by omega)) (2 ^ e)
  have hB : (∑ i ∈ Finset.range k, s ^ i) * (s - 1) = s ^ k - 1 :=
    geom_sum_mul_nat (by omega) k
  have hC : (∑ i ∈ Finset.range (2 ^ e), s ^ i) * (s - 1) = s ^ 2 ^ e - 1 :=
    geom_sum_mul_nat (by omega) (2 ^ e)
  have hD : (∑ i ∈ Finset.range k, (s ^ 2 ^ e) ^ i) * (s ^ 2 ^ e - 1) = (s ^ 2 ^ e) ^ k - 1 :=
    geom_sum_mul_nat (Nat.one_le_pow (2 ^ e) s (by omega)) k
  calc (∑ i ∈ Finset.range (2 ^ e), (s ^ k) ^ i) * (∑ i ∈ Finset.range k, s ^ i) * (s - 1)
      = (∑ i ∈ Finset.range (2 ^ e), (s ^ k) ^ i)
          * ((∑ i ∈ Finset.range k, s ^ i) * (s - 1)) := by ring
    _ = (∑ i ∈ Finset.range (2 ^ e), (s ^ k) ^ i) * (s ^ k - 1) := by rw [hB]
    _ = (s ^ k) ^ 2 ^ e - 1 := hA
    _ = (s ^ 2 ^ e) ^ k - 1 := by rw [← pow_mul, ← pow_mul, mul_comm]
    _ = (∑ i ∈ Finset.range k, (s ^ 2 ^ e) ^ i) * (s ^ 2 ^ e - 1) := hD.symm
    _ = (∑ i ∈ Finset.range (2 ^ e), s ^ i)
          * (∑ i ∈ Finset.range k, (s ^ 2 ^ e) ^ i) * (s - 1) := by
        rw [← hC]; ring

theorem le_sub_two_of_pow_mod {s e r : ℕ} (hs : Odd s) (he : 1 ≤ e)
    (h : s ^ 2 ^ e % 2 ^ (r + 1) = 2 ^ r + 1) : e + 2 ≤ r := by
  by_contra hcon
  have hle : r + 1 ≤ e + 2 := by omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
  have hdvd : 2 ^ (r + 1) ∣ s ^ 2 ^ (j + 1) - 1 := by
    have h1 : 2 ^ (j + 3) ∣ s ^ 2 ^ (j + 1) - 1 := two_pow_dvd_pow_two_pow_sub_one hs j
    have h2 : 2 ^ (r + 1) ∣ 2 ^ (j + 3) := Nat.pow_dvd_pow 2 (by omega)
    exact h2.trans h1
  have hge : 1 ≤ s ^ 2 ^ (j + 1) := Nat.one_le_pow (2 ^ (j + 1)) s (by
    obtain ⟨c, hc⟩ := hs
    omega)
  have hmod : s ^ 2 ^ (j + 1) % 2 ^ (r + 1) = 1 :=
    mod_eq_one_of_dvd_sub_one (two_pow_ne_one (by omega)) hdvd hge
  rw [hmod] at h
  have : 2 ^ r = 0 := by omega
  exact absurd this (by positivity)

theorem not_two_pow_dvd_geom_sum {s e r : ℕ} (hs : Odd s) (he : 1 ≤ e)
    (h : s ^ 2 ^ e % 2 ^ (r + 1) = 2 ^ r + 1) (k : ℕ) :
    ¬ 2 ^ r ∣ ∑ i ∈ Finset.range (2 ^ e), (s ^ k) ^ i := by
  have he2 : e + 2 ≤ r := le_sub_two_of_pow_mod hs he h
  have hs2 : 2 ≤ s := by
    have hs0 : s ≠ 0 := by
      rintro rfl
      obtain ⟨c, hc⟩ := hs
      omega
    have hs1 : s ≠ 1 := by
      rintro rfl
      rw [one_pow] at h
      have h1 : (1 : ℕ) % 2 ^ (r + 1) = 1 :=
        Nat.one_mod_eq_one.mpr (two_pow_ne_one (by omega))
      have : 2 ^ r = 0 := by omega
      exact absurd this (by positivity)
    omega
  rcases Nat.even_or_odd k with hkeven | hkodd
  · obtain ⟨m, rfl⟩ := hkeven
    intro hdiv
    obtain ⟨E, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    have hsq : s ^ (m + m) = (s ^ m) ^ 2 := by rw [pow_add, pow_two]
    have hu4 : ((s ^ m) ^ 2) % 4 = 1 := by
      have h8 : ((s ^ m) ^ 2) % 8 = 1 := odd_sq_mod_eight (hs.pow (n := m))
      rw [← Nat.mod_mod_of_dvd ((s ^ m) ^ 2) (by norm_num : 4 ∣ 8), h8]
    obtain ⟨a, ha, hGa⟩ := geom_sum_four_dvd hu4 E
    rw [hsq, hGa] at hdiv
    have hr : 2 ≤ r - (E + 1) := by omega
    rw [show r = (E + 1) + (r - (E + 1)) by omega, pow_add] at hdiv
    have hdvd : 2 ^ (r - (E + 1)) ∣ a :=
      (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ (E + 1))).mp hdiv
    have h4 : 4 ∣ a := by
      have := (Nat.pow_dvd_pow (2 : ℕ) hr).trans hdvd
      simpa using this
    have h2 : 2 ∣ a := dvd_trans (by norm_num : 2 ∣ 4) h4
    have h0 : a % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h2
    have h1 : a % 2 = 1 := Nat.odd_iff.mp ha
    omega
  · intro hdiv
    have hDodd : Odd (∑ i ∈ Finset.range k, (s ^ 2 ^ e) ^ i) :=
      geom_sum_odd (hs.pow) hkodd
    have hcross := geom_sum_cross hs2 k e
    have hB : 2 ^ r ∣ (∑ i ∈ Finset.range (2 ^ e), s ^ i)
        * (∑ i ∈ Finset.range k, (s ^ 2 ^ e) ^ i) := by
      rw [← hcross]
      exact dvd_mul_of_dvd_left hdiv _
    have hcop : (2 ^ r).Coprime (∑ i ∈ Finset.range k, (s ^ 2 ^ e) ^ i) :=
      (hDodd.coprime_two_right.symm).pow_left r
    have hCdvd : 2 ^ r ∣ ∑ i ∈ Finset.range (2 ^ e), s ^ i :=
      hcop.dvd_of_dvd_mul_right hB
    have h2dvd : 2 ∣ s - 1 := by
      obtain ⟨c, rfl⟩ := hs
      exact ⟨c, by omega⟩
    have hCmul : (∑ i ∈ Finset.range (2 ^ e), s ^ i) * (s - 1) = s ^ 2 ^ e - 1 :=
      geom_sum_mul_nat (by omega) (2 ^ e)
    have hprod : 2 ^ (r + 1) ∣ s ^ 2 ^ e - 1 := by
      have := Nat.mul_dvd_mul hCdvd h2dvd
      rw [show 2 ^ r * 2 = 2 ^ (r + 1) by rfl] at this
      rwa [hCmul] at this
    have hge : 1 ≤ s ^ 2 ^ e := Nat.one_le_pow (2 ^ e) s (by omega)
    have hmod : s ^ 2 ^ e % 2 ^ (r + 1) = 1 :=
      mod_eq_one_of_dvd_sub_one (two_pow_ne_one (by omega)) hprod hge
    rw [hmod] at h
    have : 2 ^ r = 0 := by omega
    exact absurd this (by positivity)

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big
