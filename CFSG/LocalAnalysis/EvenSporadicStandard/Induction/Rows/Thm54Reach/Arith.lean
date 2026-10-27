module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUSporSRNum
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicTableDefs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.EvenSporadicStandard.Induction.Thm54Reach

open CFSG.ComponentClassification.CatFC CFSG.ComponentClassification.GSThmB.QPUSpor

@[expose] def Thm54Order (c : ℕ) : Prop :=
  (∃ f : ℕ, 3 ≤ f ∧ Odd f ∧ c = 2 ^ (2 * f) * ((2 ^ (2 * f) + 1) * (2 ^ f - 1))) ∨
  (∃ m : ℕ, 3 ≤ m ∧ c = 2 ^ (4 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1))) ∨
  (∃ m : ℕ, 3 ≤ m ∧
    c = 2 ^ (6 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) * (2 ^ (4 * m) - 1)))) ∨
  (∃ m : ℕ, 3 ≤ m ∧
    c = 2 ^ (6 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) * (2 ^ (4 * m) - 1)))) ∨
  (∃ m d : ℕ, 3 ≤ m ∧ (d = 1 ∨ d = 5) ∧
    c * d = 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
      ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1))))) ∨
  (∃ m d : ℕ, 3 ≤ m ∧ (d = 1 ∨ d = 5) ∧
    c * d = 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
      ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1)))))

private instance (s : TauCeti.SporadicName) (c : ℕ) : Decidable (SporadicInnerRow s c) := by
  cases s <;> simp only [SporadicInnerRow] <;> infer_instance

private instance (s : TauCeti.SporadicName) (c : ℕ) : Decidable (SporadicOuterRow s c) := by
  cases s <;> simp only [SporadicOuterRow] <;> infer_instance

private theorem odd_two_pow_add_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ]
  exact ⟨2 ^ j, by ring⟩

private theorem odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hp : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by norm_num)
  rw [pow_succ]
  exact ⟨2 ^ j - 1, by omega⟩

private theorem one_le_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : 1 ≤ 2 ^ k - 1 := by
  have h : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

private theorem one_le_two_pow_add_one (k : ℕ) : 1 ≤ 2 ^ k + 1 :=
  Nat.le_add_left 1 (2 ^ k)

private theorem one_le_mul' {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
  Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp ha) (Nat.one_le_iff_ne_zero.mp hb))

private theorem two_pow_sub_one_lt (k : ℕ) : 2 ^ k - 1 < 2 ^ k := by
  have : 0 < 2 ^ k := by positivity
  omega

private theorem two_pow_add_one_le (k : ℕ) : 2 ^ k + 1 ≤ 2 ^ (k + 1) := by
  have h : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
  have hp : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
  omega

private theorem coprime_two_pow (k : ℕ) {d : ℕ} (hd : d = 1 ∨ d = 5) :
    Nat.Coprime (2 ^ k) d := by
  rcases hd with rfl | rfl
  · exact Nat.coprime_one_right _
  · exact Nat.Coprime.pow_left _ (by decide)

private theorem Thm54Order.exists_two_pow_mul_odd {c : ℕ} (hc : Thm54Order c) :
    ∃ V r : ℕ, Even V ∧ c = 2 ^ V * r ∧ Odd r := by
  rcases hc with ⟨f, hf, _, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ |
    ⟨m, d, hm, hd, hcd⟩ | ⟨m, d, hm, hd, hcd⟩
  · exact ⟨2 * f, (2 ^ (2 * f) + 1) * (2 ^ f - 1), ⟨f, by ring⟩, rfl,
      (odd_two_pow_add_one (by omega)).mul (odd_two_pow_sub_one (by omega))⟩
  · exact ⟨4 * m, (2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1), ⟨2 * m, by ring⟩, rfl,
      (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))⟩
  · exact ⟨6 * m, (2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) * (2 ^ (4 * m) - 1)),
      ⟨3 * m, by ring⟩, rfl,
      (odd_two_pow_sub_one (by omega)).mul
        ((odd_two_pow_add_one (by omega)).mul (odd_two_pow_sub_one (by omega)))⟩
  · exact ⟨6 * m, (2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) * (2 ^ (4 * m) - 1)),
      ⟨3 * m, by ring⟩, rfl,
      (odd_two_pow_sub_one (by omega)).mul
        ((odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega)))⟩
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hdvd : 2 ^ (10 * m) ∣ c :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have hRodd : Odd ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
        ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1)))) :=
      (odd_two_pow_sub_one (by omega)).mul
        ((odd_two_pow_add_one (by omega)).mul
          ((odd_two_pow_sub_one (by omega)).mul (odd_two_pow_add_one (by omega))))
    have hrd : (c / 2 ^ (10 * m)) * d = (2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
        ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1))) := by
      have h1 : 2 ^ (10 * m) * ((c / 2 ^ (10 * m)) * d) = 2 ^ (10 * m) *
          ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
            ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1)))) := by
        rw [← mul_assoc, Nat.mul_div_cancel' hdvd, hcd]
      exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by norm_num)) h1
    refine ⟨10 * m, c / 2 ^ (10 * m), ⟨5 * m, by ring⟩,
      (Nat.mul_div_cancel' hdvd).symm, ?_⟩
    exact Nat.Odd.of_mul_left (hrd.symm ▸ hRodd)
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hdvd : 2 ^ (10 * m) ∣ c :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have hRodd : Odd ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
        ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1)))) :=
      (odd_two_pow_sub_one (by omega)).mul
        ((odd_two_pow_sub_one (by omega)).mul
          ((odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))))
    have hrd : (c / 2 ^ (10 * m)) * d = (2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
        ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1))) := by
      have h1 : 2 ^ (10 * m) * ((c / 2 ^ (10 * m)) * d) = 2 ^ (10 * m) *
          ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
            ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1)))) := by
        rw [← mul_assoc, Nat.mul_div_cancel' hdvd, hcd]
      exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by norm_num)) h1
    refine ⟨10 * m, c / 2 ^ (10 * m), ⟨5 * m, by ring⟩,
      (Nat.mul_div_cancel' hdvd).symm, ?_⟩
    exact Nat.Odd.of_mul_left (hrd.symm ▸ hRodd)

private theorem not_two_pow_42_dvd_sporOrder {s : TauCeti.SporadicName} (hs : s ≠ .M) :
    ¬ 2 ^ 42 ∣ sporOrder s := by
  cases s <;> simp only [sporOrder, sporFactors] <;> first | decide | exact absurd rfl hs

private theorem two_pow_le_factorial_sq {k : ℕ} (hk : 14 ≤ k) :
    2 ^ (6 * k - 20) ≤ k.factorial ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hsq : (n + 1).factorial ^ 2 = (n + 1) ^ 2 * n.factorial ^ 2 := by
        rw [Nat.factorial_succ]; ring
      rw [hsq]
      calc 2 ^ (6 * (n + 1) - 20) = 2 ^ 6 * 2 ^ (6 * n - 20) := by
            rw [← pow_add]; congr 1; omega
        _ = 64 * 2 ^ (6 * n - 20) := by norm_num
        _ ≤ 64 * n.factorial ^ 2 := Nat.mul_le_mul_left _ ih
        _ ≤ (n + 1) ^ 2 * n.factorial ^ 2 :=
            Nat.mul_le_mul (by nlinarith [hn]) (le_refl _)

private theorem three_dvd_factorial_div_two {k : ℕ} (hk : 5 ≤ k) : 3 ∣ k.factorial / 2 := by
  have h6 : 6 ∣ k.factorial := by
    rcases Nat.lt_or_ge k 6 with hk5 | hk6
    · have : k = 5 := by omega
      subst this
      norm_num
    · exact Nat.dvd_factorial (m := 6) (n := k) (by norm_num) hk6
  obtain ⟨t, ht⟩ := h6
  refine ⟨t, ?_⟩
  rw [ht, show 6 * t = 2 * (3 * t) by ring]
  exact Nat.mul_div_right (3 * t) (by norm_num)

private theorem factorial_div_two_ne {V c k : ℕ} (hV : 12 ≤ V) (hdvd : 2 ^ V ∣ c)
    (hlt : c < 2 ^ (3 * V - 5)) (hk2 : 2 ≤ k) (hk : k.factorial / 2 = c) : False := by
  have h2dvd : 2 ∣ k.factorial := Nat.dvd_factorial (m := 2) (by norm_num) hk2
  have hfact : k.factorial = 2 * c := by
    rw [← hk]
    exact (Nat.mul_div_cancel' h2dvd).symm
  have hpow : 2 ^ (V + 1) ∣ k.factorial := by
    rw [hfact, pow_succ, mul_comm 2 c]
    exact Nat.mul_dvd_mul_right hdvd 2
  have hk0 : k ≠ 0 := by omega
  have h1 : V + 1 ≤ padicValNat 2 k.factorial :=
    (padicValNat_dvd_iff_le (p := 2) (Nat.factorial_ne_zero k)).1 hpow
  have h2 : padicValNat 2 k.factorial < k := padicValNat_factorial_lt_of_ne_zero 2 hk0
  have hkV : V + 2 ≤ k := by omega
  have hbase : 2 ^ (6 * k - 20) ≤ k.factorial ^ 2 := two_pow_le_factorial_sq (by omega)
  have hle : 2 ^ (6 * V - 8) ≤ k.factorial ^ 2 := by
    calc 2 ^ (6 * V - 8) ≤ 2 ^ (6 * k - 20) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ k.factorial ^ 2 := hbase
  have hlt2 : k.factorial ^ 2 < 2 ^ (6 * V - 8) := by
    rw [hfact]
    have hc2 : c ^ 2 < 2 ^ (6 * V - 10) := by
      calc c ^ 2 < (2 ^ (3 * V - 5)) ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
        _ = 2 ^ (2 * (3 * V - 5)) := by rw [← pow_mul]; congr 1; ring
        _ = 2 ^ (6 * V - 10) := by congr 1; omega
    calc (2 * c) ^ 2 = 4 * c ^ 2 := by ring
      _ < 4 * 2 ^ (6 * V - 10) := Nat.mul_lt_mul_of_pos_left hc2 (by norm_num)
      _ = 2 ^ (6 * V - 8) := by
          rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_add]
          congr 1; omega
  omega

theorem Thm54Order.ge {c : ℕ} (hc : Thm54Order c) : 29120 ≤ c := by
  rcases hc with ⟨f, hf, _, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ |
    ⟨m, d, hm, hd, hcd⟩ | ⟨m, d, hm, hd, hcd⟩
  · have h1 : 64 ≤ 2 ^ (2 * f) := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 65 ≤ 2 ^ (2 * f) + 1 := by omega
    have h3 : 7 ≤ 2 ^ f - 1 := by
      have : 8 ≤ 2 ^ f := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      omega
    calc 29120 = 64 * (65 * 7) := by norm_num
      _ ≤ 2 ^ (2 * f) * ((2 ^ (2 * f) + 1) * (2 ^ f - 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  · have h1 : 4096 ≤ 2 ^ (4 * m) := by
      calc 4096 = 2 ^ 12 := by norm_num
        _ ≤ 2 ^ (4 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 63 ≤ 2 ^ (2 * m) - 1 := by
      have : 64 ≤ 2 ^ (2 * m) := by
        calc 64 = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h3 : 1 ≤ 2 ^ (4 * m) - 1 := one_le_two_pow_sub_one (by omega)
    calc 29120 ≤ 4096 * (63 * 1) := by norm_num
      _ ≤ 2 ^ (4 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1)) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  · have h1 : 29120 ≤ 2 ^ (6 * m) := by
      calc 29120 ≤ 2 ^ 18 := by norm_num
        _ ≤ 2 ^ (6 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 1 ≤ 2 ^ (2 * m) - 1 := one_le_two_pow_sub_one (by omega)
    have h3 : 1 ≤ 2 ^ (3 * m) + 1 := one_le_two_pow_add_one _
    have h4 : 1 ≤ 2 ^ (4 * m) - 1 := one_le_two_pow_sub_one (by omega)
    calc 29120 = 29120 * (1 * (1 * 1)) := by norm_num
      _ ≤ 2 ^ (6 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) * (2 ^ (4 * m) - 1))) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 (Nat.mul_le_mul h3 h4))
  · have h1 : 29120 ≤ 2 ^ (6 * m) := by
      calc 29120 ≤ 2 ^ 18 := by norm_num
        _ ≤ 2 ^ (6 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 1 ≤ 2 ^ (2 * m) - 1 := one_le_two_pow_sub_one (by omega)
    have h3 : 1 ≤ 2 ^ (3 * m) - 1 := one_le_two_pow_sub_one (by omega)
    have h4 : 1 ≤ 2 ^ (4 * m) - 1 := one_le_two_pow_sub_one (by omega)
    calc 29120 = 29120 * (1 * (1 * 1)) := by norm_num
      _ ≤ 2 ^ (6 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) * (2 ^ (4 * m) - 1))) :=
        Nat.mul_le_mul h1 (Nat.mul_le_mul h2 (Nat.mul_le_mul h3 h4))
  · have hR : 1 ≤ (2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
        ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1))) :=
      one_le_mul' (one_le_two_pow_sub_one (by omega))
        (one_le_mul' (one_le_two_pow_add_one _)
          (one_le_mul' (one_le_two_pow_sub_one (by omega)) (one_le_two_pow_add_one _)))
    have hNum : 2 ^ 30 ≤ 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
        ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1)))) := by
      calc 2 ^ 30 ≤ 2 ^ (10 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ (10 * m) * 1 := by ring
        _ ≤ 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
            ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1)))) := Nat.mul_le_mul_left _ hR
    have hcle : (2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
        ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1))))) / 5 ≤ c :=
      Nat.div_le_of_le_mul (by
        calc 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
              ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1)))) = c * d := hcd.symm
          _ ≤ c * 5 := Nat.mul_le_mul_left c (by rcases hd with rfl | rfl <;> norm_num)
          _ = 5 * c := by ring)
    have h29120 : 29120 ≤ (2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
        ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1))))) / 5 :=
      (Nat.le_div_iff_mul_le (by norm_num : 0 < 5)).2 (le_trans (by norm_num) hNum)
    exact le_trans h29120 hcle
  · have hR : 1 ≤ (2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
        ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1))) :=
      one_le_mul' (one_le_two_pow_sub_one (by omega))
        (one_le_mul' (one_le_two_pow_sub_one (by omega))
          (one_le_mul' (one_le_two_pow_sub_one (by omega)) (one_le_two_pow_sub_one (by omega))))
    have hNum : 2 ^ 30 ≤ 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
        ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1)))) := by
      calc 2 ^ 30 ≤ 2 ^ (10 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ (10 * m) * 1 := by ring
        _ ≤ 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
            ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1)))) := Nat.mul_le_mul_left _ hR
    have hcle : (2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
        ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1))))) / 5 ≤ c :=
      Nat.div_le_of_le_mul (by
        calc 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
              ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1)))) = c * d := hcd.symm
          _ ≤ c * 5 := Nat.mul_le_mul_left c (by rcases hd with rfl | rfl <;> norm_num)
          _ = 5 * c := by ring)
    have h29120 : 29120 ≤ (2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
        ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1))))) / 5 :=
      (Nat.le_div_iff_mul_le (by norm_num : 0 < 5)).2 (le_trans (by norm_num) hNum)
    exact le_trans h29120 hcle

theorem Thm54Order.ne_he {c : ℕ} (hc : Thm54Order c) : c ≠ 4030387200 := by
  intro h
  have hnot : ¬ 2 ^ 11 ∣ 4030387200 := by norm_num
  rcases hc with ⟨f, hf, hodd, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ |
    ⟨m, d, hm, hd, hcd⟩ | ⟨m, d, hm, hd, hcd⟩
  · have hd : 2 ^ (2 * f) ∣ 4030387200 := by rw [← h]; exact dvd_mul_right _ _
    have hf10 : 2 * f ≤ 10 := by
      by_contra hc'
      exact hnot ((Nat.pow_dvd_pow 2 (by omega : 11 ≤ 2 * f)).trans hd)
    have hf5 : f ≤ 5 := by omega
    obtain ⟨j, hj⟩ := hodd
    have hf35 : f = 3 ∨ f = 5 := by omega
    rcases hf35 with rfl | rfl <;> norm_num at h
  · have hd : 2 ^ (4 * m) ∣ 4030387200 := by rw [← h]; exact dvd_mul_right _ _
    exact hnot ((Nat.pow_dvd_pow 2 (by omega : 11 ≤ 4 * m)).trans hd)
  · have hd : 2 ^ (6 * m) ∣ 4030387200 := by rw [← h]; exact dvd_mul_right _ _
    exact hnot ((Nat.pow_dvd_pow 2 (by omega : 11 ≤ 6 * m)).trans hd)
  · have hd : 2 ^ (6 * m) ∣ 4030387200 := by rw [← h]; exact dvd_mul_right _ _
    exact hnot ((Nat.pow_dvd_pow 2 (by omega : 11 ≤ 6 * m)).trans hd)
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hdvd : 2 ^ (10 * m) ∣ c :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have hd : 2 ^ (10 * m) ∣ 4030387200 := by rw [← h]; exact hdvd
    exact hnot ((Nat.pow_dvd_pow 2 (by omega : 11 ≤ 10 * m)).trans hd)
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hdvd : 2 ^ (10 * m) ∣ c :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have hd : 2 ^ (10 * m) ∣ 4030387200 := by rw [← h]; exact hdvd
    exact hnot ((Nat.pow_dvd_pow 2 (by omega : 11 ≤ 10 * m)).trans hd)

theorem Thm54Order.ne_factorial_div_two {c : ℕ} (hc : Thm54Order c) {k : ℕ} (hk : 5 ≤ k) :
    k.factorial / 2 ≠ c := by
  intro h
  have h3k : 3 ∣ k.factorial / 2 := three_dvd_factorial_div_two hk
  rcases hc with ⟨f, hf, hodd, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ |
    ⟨m, d, hm, hd, hcd⟩ | ⟨m, d, hm, hd, hcd⟩
  · by_cases hf7 : 7 ≤ f
    · refine factorial_div_two_ne (V := 2 * f) (by omega) (dvd_mul_right _ _) ?_ (by omega) h
      calc 2 ^ (2 * f) * ((2 ^ (2 * f) + 1) * (2 ^ f - 1))
          < 2 ^ (2 * f) * (2 ^ (2 * f + 1) * 2 ^ f) :=
            Nat.mul_lt_mul_of_pos_left
              (Nat.mul_lt_mul_of_le_of_lt (two_pow_add_one_le _) (two_pow_sub_one_lt _)
                (Nat.pow_pos (by norm_num))) (Nat.pow_pos (by norm_num))
        _ = 2 ^ (5 * f + 1) := by rw [← pow_add, ← pow_add]; congr 1; ring
        _ ≤ 2 ^ (3 * (2 * f) - 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · obtain ⟨j, hj⟩ := hodd
      have hf5 : f ≤ 5 := by omega
      have hf35 : f = 3 ∨ f = 5 := by omega
      rcases hf35 with rfl | rfl
      · rw [h] at h3k
        norm_num at h3k
      · rw [h] at h3k
        norm_num at h3k
  · refine factorial_div_two_ne (V := 4 * m) (by omega) (dvd_mul_right _ _) ?_ (by omega) h
    calc 2 ^ (4 * m) * ((2 ^ (2 * m) - 1) * (2 ^ (4 * m) - 1))
        < 2 ^ (4 * m) * (2 ^ (2 * m) * 2 ^ (4 * m)) :=
          Nat.mul_lt_mul_of_pos_left
            (Nat.mul_lt_mul_of_lt_of_lt (two_pow_sub_one_lt _) (two_pow_sub_one_lt _))
            (Nat.pow_pos (by norm_num))
      _ = 2 ^ (10 * m) := by rw [← pow_add, ← pow_add]; congr 1; ring
      _ ≤ 2 ^ (3 * (4 * m) - 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · refine factorial_div_two_ne (V := 6 * m) (by omega) (dvd_mul_right _ _) ?_ (by omega) h
    calc 2 ^ (6 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) * (2 ^ (4 * m) - 1)))
        < 2 ^ (6 * m) * (2 ^ (2 * m) * (2 ^ (3 * m + 1) * 2 ^ (4 * m))) :=
          Nat.mul_lt_mul_of_pos_left
            (Nat.mul_lt_mul_of_lt_of_lt (two_pow_sub_one_lt _)
              (Nat.mul_lt_mul_of_le_of_lt (two_pow_add_one_le _) (two_pow_sub_one_lt _)
                (Nat.pow_pos (by norm_num)))) (Nat.pow_pos (by norm_num))
      _ = 2 ^ (15 * m + 1) := by rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring
      _ ≤ 2 ^ (3 * (6 * m) - 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · refine factorial_div_two_ne (V := 6 * m) (by omega) (dvd_mul_right _ _) ?_ (by omega) h
    calc 2 ^ (6 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) * (2 ^ (4 * m) - 1)))
        < 2 ^ (6 * m) * (2 ^ (2 * m) * (2 ^ (3 * m) * 2 ^ (4 * m))) :=
          Nat.mul_lt_mul_of_pos_left
            (Nat.mul_lt_mul_of_lt_of_lt (two_pow_sub_one_lt _)
              (Nat.mul_lt_mul_of_lt_of_lt (two_pow_sub_one_lt _) (two_pow_sub_one_lt _)))
            (Nat.pow_pos (by norm_num))
      _ = 2 ^ (15 * m) := by rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring
      _ ≤ 2 ^ (3 * (6 * m) - 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hdvd : 2 ^ (10 * m) ∣ c :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have hle : c ≤ 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
        ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1)))) := by
      calc c ≤ c * d := Nat.le_mul_of_pos_right c (by rcases hd with rfl | rfl <;> norm_num)
        _ = 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
            ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1)))) := hcd
    refine factorial_div_two_ne (V := 10 * m) (by omega) hdvd ?_ (by omega) h
    refine lt_of_le_of_lt hle ?_
    calc 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
            ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1))))
        < 2 ^ (10 * m) * (2 ^ (2 * m) * (2 ^ (3 * m + 1) * (2 ^ (4 * m) * 2 ^ (5 * m + 1)))) :=
          Nat.mul_lt_mul_of_pos_left
            (Nat.mul_lt_mul_of_lt_of_lt (two_pow_sub_one_lt _)
              (Nat.mul_lt_mul_of_le_of_lt (two_pow_add_one_le _)
                (Nat.mul_lt_mul_of_lt_of_le (two_pow_sub_one_lt _) (two_pow_add_one_le _)
                  (Nat.pow_pos (by norm_num)))
                (Nat.pow_pos (by norm_num))))
            (Nat.pow_pos (by norm_num))
      _ = 2 ^ (24 * m + 2) := by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
      _ ≤ 2 ^ (3 * (10 * m) - 5) :=
          Nat.pow_le_pow_right (by norm_num) (by omega : 24 * m + 2 ≤ 3 * (10 * m) - 5)
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have hdvd : 2 ^ (10 * m) ∣ c :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have hle : c ≤ 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
        ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1)))) := by
      calc c ≤ c * d := Nat.le_mul_of_pos_right c (by rcases hd with rfl | rfl <;> norm_num)
        _ = 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
            ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1)))) := hcd
    refine factorial_div_two_ne (V := 10 * m) (by omega) hdvd ?_ (by omega) h
    refine lt_of_le_of_lt hle ?_
    calc 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
            ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1))))
        < 2 ^ (10 * m) * (2 ^ (2 * m) * (2 ^ (3 * m) * (2 ^ (4 * m) * 2 ^ (5 * m)))) :=
          Nat.mul_lt_mul_of_pos_left
            (Nat.mul_lt_mul_of_lt_of_lt (two_pow_sub_one_lt _)
              (Nat.mul_lt_mul_of_lt_of_lt (two_pow_sub_one_lt _)
                (Nat.mul_lt_mul_of_lt_of_lt (two_pow_sub_one_lt _) (two_pow_sub_one_lt _))))
            (Nat.pow_pos (by norm_num))
      _ = 2 ^ (24 * m) := by rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
      _ ≤ 2 ^ (3 * (10 * m) - 5) :=
          Nat.pow_le_pow_right (by norm_num) (by omega : 24 * m ≤ 3 * (10 * m) - 5)

theorem Thm54Order.spor {c : ℕ} (hc : Thm54Order c) {s : TauCeti.SporadicName} (hs : s ≠ .M)
    (hdvd : c ∣ sporOrder s) (hrow : SporadicInnerRow s c ∨ SporadicOuterRow s c) : s = .Ru := by
  have hM : ¬ 2 ^ 42 ∣ sporOrder s := not_two_pow_42_dvd_sporOrder hs
  rcases hc with ⟨f, hf, hodd, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ |
    ⟨m, d, hm, hd, hcd⟩ | ⟨m, d, hm, hd, hcd⟩
  · have h2 : 2 ^ (2 * f) ∣ sporOrder s := (dvd_mul_right _ _).trans hdvd
    have hf20 : f ≤ 20 := by
      by_contra hc'
      exact hM ((Nat.pow_dvd_pow 2 (by omega : 42 ≤ 2 * f)).trans h2)
    interval_cases f
    all_goals first
      | exact absurd hodd (by decide)
      | (revert hs hdvd hrow s; decide)
  · have h2 : 2 ^ (4 * m) ∣ sporOrder s := (dvd_mul_right _ _).trans hdvd
    have hm10 : m ≤ 10 := by
      by_contra hc'
      exact hM ((Nat.pow_dvd_pow 2 (by omega : 42 ≤ 4 * m)).trans h2)
    interval_cases m <;> (revert hs hdvd hrow s; decide)
  · have h2 : 2 ^ (6 * m) ∣ sporOrder s := (dvd_mul_right _ _).trans hdvd
    have hm6 : m ≤ 6 := by
      by_contra hc'
      exact hM ((Nat.pow_dvd_pow 2 (by omega : 42 ≤ 6 * m)).trans h2)
    interval_cases m <;> (revert hs hdvd hrow s; decide)
  · have h2 : 2 ^ (6 * m) ∣ sporOrder s := (dvd_mul_right _ _).trans hdvd
    have hm6 : m ≤ 6 := by
      by_contra hc'
      exact hM ((Nat.pow_dvd_pow 2 (by omega : 42 ≤ 6 * m)).trans h2)
    interval_cases m <;> (revert hs hdvd hrow s; decide)
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have h2 : 2 ^ (10 * m) ∣ c :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have h2' : 2 ^ (10 * m) ∣ sporOrder s := h2.trans hdvd
    have hm4 : m ≤ 4 := by
      by_contra hc'
      exact hM ((Nat.pow_dvd_pow 2 (by omega : 42 ≤ 10 * m)).trans h2')
    rcases hd with rfl | rfl
    · have hce : c = 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
          ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1)))) := by simpa using hcd
      rw [hce] at hdvd hrow
      interval_cases m <;> (revert hs hdvd hrow s; decide)
    · have hce : c = (2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) + 1) *
          ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) + 1))))) / 5 :=
        Nat.eq_div_of_mul_eq_left (by norm_num) hcd
      rw [hce] at hdvd hrow
      interval_cases m <;> (revert hs hdvd hrow s; decide)
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have h2 : 2 ^ (10 * m) ∣ c :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have h2' : 2 ^ (10 * m) ∣ sporOrder s := h2.trans hdvd
    have hm4 : m ≤ 4 := by
      by_contra hc'
      exact hM ((Nat.pow_dvd_pow 2 (by omega : 42 ≤ 10 * m)).trans h2')
    rcases hd with rfl | rfl
    · have hce : c = 2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
          ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1)))) := by simpa using hcd
      rw [hce] at hdvd hrow
      interval_cases m <;> (revert hs hdvd hrow s; decide)
    · have hce : c = (2 ^ (10 * m) * ((2 ^ (2 * m) - 1) * ((2 ^ (3 * m) - 1) *
          ((2 ^ (4 * m) - 1) * (2 ^ (5 * m) - 1))))) / 5 :=
        Nat.eq_div_of_mul_eq_left (by norm_num) hcd
      rw [hce] at hdvd hrow
      interval_cases m <;> (revert hs hdvd hrow s; decide)

theorem Thm54Order.not_monster_row {c : ℕ} (hc : Thm54Order c) :
    ¬ (2 ^ 41 ∣ c ∧ ¬ 2 ^ 42 ∣ c) := by
  obtain ⟨V, r, hEven, hcV, hrodd⟩ := hc.exists_two_pow_mul_odd
  rintro ⟨h41, h42⟩
  by_cases hV : 42 ≤ V
  · exact h42 (hcV ▸ (Nat.pow_dvd_pow 2 hV).trans (dvd_mul_right _ _))
  · have hV40 : V ≤ 40 := by obtain ⟨k, rfl⟩ := hEven; omega
    have h41' : 2 ^ 41 ∣ 2 ^ V * r := hcV ▸ h41
    have hpow : 2 ^ 41 = 2 ^ V * 2 ^ (41 - V) := by rw [← pow_add]; congr 1; omega
    have hd : 2 ^ (41 - V) ∣ r := by
      have : 2 ^ V * 2 ^ (41 - V) ∣ 2 ^ V * r := by rw [← hpow]; exact h41'
      exact Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos (by norm_num)) this
    have hpos : 1 ≤ 41 - V := by omega
    exact hrodd.not_two_dvd_nat ((Nat.pow_dvd_pow 2 hpos).trans hd)

theorem Thm54Order.ru {c : ℕ} (hc : Thm54Order c) (hdvd : c ∣ 145926144000) (h29 : ¬ 29 ∣ c) :
    c = 29120 := by
  have hnot : ¬ 2 ^ 15 ∣ 145926144000 := by norm_num
  rcases hc with ⟨f, hf, hodd, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ |
    ⟨m, d, hm, hd, hcd⟩ | ⟨m, d, hm, hd, hcd⟩
  · have h2 : 2 ^ (2 * f) ∣ 145926144000 := (dvd_mul_right _ _).trans hdvd
    have hf14 : 2 * f ≤ 14 := by
      by_contra hc'
      exact hnot ((Nat.pow_dvd_pow 2 (by omega : 15 ≤ 2 * f)).trans h2)
    have hf7 : f ≤ 7 := by omega
    obtain ⟨j, hj⟩ := hodd
    have hf357 : f = 3 ∨ f = 5 ∨ f = 7 := by omega
    rcases hf357 with rfl | rfl | rfl
    · norm_num
    · norm_num at hdvd
    · norm_num at h29
  · have h2 : 2 ^ (4 * m) ∣ 145926144000 := (dvd_mul_right _ _).trans hdvd
    have hm3 : m ≤ 3 := by
      by_contra hc'
      exact hnot ((Nat.pow_dvd_pow 2 (by omega : 15 ≤ 4 * m)).trans h2)
    have hm3' : m = 3 := by omega
    subst m
    norm_num at hdvd
  · have h2 : 2 ^ (6 * m) ∣ 145926144000 := (dvd_mul_right _ _).trans hdvd
    exact absurd ((Nat.pow_dvd_pow 2 (by omega : 15 ≤ 6 * m)).trans h2) hnot
  · have h2 : 2 ^ (6 * m) ∣ 145926144000 := (dvd_mul_right _ _).trans hdvd
    exact absurd ((Nat.pow_dvd_pow 2 (by omega : 15 ≤ 6 * m)).trans h2) hnot
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have h2 : 2 ^ (10 * m) ∣ c :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have h2' : 2 ^ (10 * m) ∣ 145926144000 := h2.trans hdvd
    exact absurd ((Nat.pow_dvd_pow 2 (by omega : 15 ≤ 10 * m)).trans h2') hnot
  · have hcop : Nat.Coprime (2 ^ (10 * m)) d := coprime_two_pow _ hd
    have h2 : 2 ^ (10 * m) ∣ c :=
      hcop.dvd_of_dvd_mul_right (by rw [hcd]; exact dvd_mul_right _ _)
    have h2' : 2 ^ (10 * m) ∣ 145926144000 := h2.trans hdvd
    exact absurd ((Nat.pow_dvd_pow 2 (by omega : 15 ≤ 10 * m)).trans h2') hnot

end CFSG.EvenSporadicStandard.Induction.Thm54Reach
