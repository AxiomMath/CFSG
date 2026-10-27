module

public import CFSG.HardMathSupport.Lang.AnisoE8.D8ModFacts
public import CFSG.Open.Defs

public section

namespace CFSG.HardMathSupport.Lang.AnisoE8

@[expose] def N8 (q : ℕ) : ℕ :=
  q ^ (8 * (8 - 1)) * (q ^ 8 - 1) * ∏ i ∈ Finset.Icc 1 (8 - 1), (q ^ (2 * i) - 1)

theorem N8_eq (q : ℕ) : N8 q = q ^ 56 * (q ^ 8 - 1) *
    ((q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 8 - 1) * (q ^ 10 - 1) * (q ^ 12 - 1) *
      (q ^ 14 - 1)) := by
  simp [N8, Finset.prod_Icc_succ_top]

theorem two_le_of_orderOf_eq_eight {P q : ℕ} (hq : 1 ≤ q) (he : orderOf (q : ZMod P) = 8) :
    2 ≤ q := by
  by_contra h
  have : q = 1 := by omega
  subst this
  rw [Nat.cast_one, orderOf_one] at he
  omega

theorem factorization_mul_eq_left {P a b : ℕ} (ha : a ≠ 0) (hb : ¬ P ∣ b) :
    (a * b).factorization P = a.factorization P := by
  have hb0 : b ≠ 0 := fun h => hb (h ▸ dvd_zero P)
  rw [Nat.factorization_mul ha hb0, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hb,
    add_zero]

section

variable {P q : ℕ} (hP : P.Prime) (hq : 1 ≤ q) (he : orderOf (q : ZMod P) = 8)

include hP hq he

theorem not_dvd_pow_sub_one_of_not_dvd {k : ℕ} (hk : ¬ 8 ∣ k) : ¬ P ∣ q ^ k - 1 :=
  fun h => hk ((dvd_pow_sub_one_iff hP hq he k).1 h)

omit hP in
theorem pow_sub_one_ne_zero {k : ℕ} (hk : 0 < k) : q ^ k - 1 ≠ 0 := by
  have := Nat.one_lt_pow hk.ne' (show 1 < q from two_le_of_orderOf_eq_eight hq he)
  omega

theorem factorization_pow_24 :
    (q ^ 24 - 1).factorization P = (q ^ 8 - 1).factorization P := by
  have hq8 : 1 ≤ q ^ 8 := Nat.one_le_pow _ _ hq
  have e : q ^ 24 - 1 = (q ^ 8 - 1) * (q ^ 16 + q ^ 8 + 1) := by
    zify [hq8, Nat.one_le_pow 24 q hq]
    ring
  rw [e]
  exact factorization_mul_eq_left (pow_sub_one_ne_zero hq he (by norm_num))
    (not_dvd_q16 hP hq he)

theorem factorization_ordE8_eq :
    (CFSG.Open.ordE8 q).factorization P = 2 * (q ^ 8 - 1).factorization P := by
  have hnd : ∀ k, ¬ 8 ∣ k → ¬ P ∣ q ^ k - 1 := fun k hk =>
    not_dvd_pow_sub_one_of_not_dvd hP hq he hk
  have e : CFSG.Open.ordE8 q = ((q ^ 24 - 1) * (q ^ 8 - 1)) *
      (q ^ 120 * (q ^ 30 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) *
        (q ^ 2 - 1)) := by
    unfold CFSG.Open.ordE8
    ring
  have hR : ¬ P ∣ q ^ 120 * (q ^ 30 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
      (q ^ 12 - 1) * (q ^ 2 - 1) := by
    simp only [hP.dvd_mul, not_or]
    exact ⟨⟨⟨⟨⟨⟨not_dvd_pow_of_orderOf_eq_eight hP he _, hnd 30 (by norm_num)⟩, hnd 20 (by norm_num)⟩,
      hnd 18 (by norm_num)⟩, hnd 14 (by norm_num)⟩, hnd 12 (by norm_num)⟩, hnd 2 (by norm_num)⟩
  rw [e, factorization_mul_eq_left (mul_ne_zero (pow_sub_one_ne_zero hq he (by norm_num))
    (pow_sub_one_ne_zero hq he (by norm_num))) hR,
    Nat.factorization_mul (pow_sub_one_ne_zero hq he (by norm_num))
      (pow_sub_one_ne_zero hq he (by norm_num)), Finsupp.add_apply,
    factorization_pow_24 hP hq he]
  ring

theorem factorization_N8_eq : (N8 q).factorization P = 2 * (q ^ 8 - 1).factorization P := by
  have hnd : ∀ k, ¬ 8 ∣ k → ¬ P ∣ q ^ k - 1 := fun k hk =>
    not_dvd_pow_sub_one_of_not_dvd hP hq he hk
  have e : N8 q = ((q ^ 8 - 1) * (q ^ 8 - 1)) *
      (q ^ 56 * (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 10 - 1) * (q ^ 12 - 1) *
        (q ^ 14 - 1)) := by
    rw [N8_eq]
    ring
  have hR : ¬ P ∣ q ^ 56 * (q ^ 2 - 1) * (q ^ 4 - 1) * (q ^ 6 - 1) * (q ^ 10 - 1) *
      (q ^ 12 - 1) * (q ^ 14 - 1) := by
    simp only [hP.dvd_mul, not_or]
    exact ⟨⟨⟨⟨⟨⟨not_dvd_pow_of_orderOf_eq_eight hP he _, hnd 2 (by norm_num)⟩, hnd 4 (by norm_num)⟩,
      hnd 6 (by norm_num)⟩, hnd 10 (by norm_num)⟩, hnd 12 (by norm_num)⟩, hnd 14 (by norm_num)⟩
  have h8 := pow_sub_one_ne_zero hq he (k := 8) (by norm_num)
  rw [e, factorization_mul_eq_left (mul_ne_zero h8 h8) hR, Nat.factorization_mul h8 h8,
    Finsupp.add_apply]
  ring

theorem factorization_ordE8_le_N8 :
    (CFSG.Open.ordE8 q).factorization P ≤ (N8 q).factorization P :=
  (factorization_ordE8_eq hP hq he).trans_le (factorization_N8_eq hP hq he).ge

end

end CFSG.HardMathSupport.Lang.AnisoE8
