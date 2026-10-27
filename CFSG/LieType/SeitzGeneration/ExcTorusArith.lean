module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.LieType.SeitzGeneration

open Polynomial

theorem dvd_pow_sub_one_iff_orderOf {p q e d : ℕ} (hq : 1 ≤ q) (he : orderOf (q : ZMod p) = e) :
    p ∣ q ^ d - 1 ↔ e ∣ d := by
  rw [← he, orderOf_dvd_iff_pow_eq_one, ← ZMod.natCast_eq_zero_iff,
    Nat.cast_sub (Nat.one_le_pow _ _ hq), sub_eq_zero]
  simp

theorem ordProj_eq_one_of_not_dvd' {p n : ℕ} (h : ¬ p ∣ n) : p ^ n.factorization p = 1 := by
  rw [Nat.factorization_eq_zero_of_not_dvd h, pow_zero]

theorem orderOf_natCast_ne_zero {p q : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) :
    orderOf (q : ZMod p) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)
  intro h
  have h' := h ▸ ZMod.orderOf_dvd_card_sub_one hq0
  have := hp.one_lt
  rw [zero_dvd_iff] at h'
  omega

theorem ordProj_pow_sub_one_of_not_dvd {p q e d : ℕ} (hq : 1 ≤ q)
    (he : orderOf (q : ZMod p) = e) (hd : ¬ e ∣ d) : p ^ (q ^ d - 1).factorization p = 1 :=
  ordProj_eq_one_of_not_dvd' fun h => hd ((dvd_pow_sub_one_iff_orderOf hq he).1 h)

theorem ordProj_pow_sub_one_of_dvd {p q e k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ q)
    (hq : 2 ≤ q) (he : orderOf (q : ZMod p) = e) (hk : k ≠ 0) :
    p ^ (q ^ (e * k) - 1).factorization p =
      p ^ (q ^ e - 1).factorization p * p ^ k.factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ q ^ e - 1 := (dvd_pow_sub_one_iff_orderOf (by omega) he).2 dvd_rfl
  have he0 : e ≠ 0 := by
    rintro rfl
    have hq0 : (q : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)
    have h := he ▸ ZMod.orderOf_dvd_card_sub_one hq0
    have := hp.one_lt
    rw [zero_dvd_iff] at h
    omega
  have h1 : 1 < q ^ e := Nat.one_lt_pow he0 (by omega)
  have hpq' : ¬ p ∣ q ^ e := fun h => hpq (hp.dvd_of_dvd_pow h)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have := padicValNat.pow_sub_pow (x := q ^ e) (y := 1) (p := p) hodd h1 (by simpa using hdvd)
    hpq' (n := k) hk
  rw [one_pow, ← pow_mul] at this
  have hne1 : q ^ (e * k) - 1 ≠ 0 := by
    have : 1 < q ^ (e * k) := Nat.one_lt_pow (mul_ne_zero he0 hk) (by omega)
    omega
  have hne2 : q ^ e - 1 ≠ 0 := by omega
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, Nat.factorization_def _ hp, this,
    pow_add]

theorem not_dvd_cyclotomic_eval_of_properDivisor {p q e i : ℕ} (hq : 1 ≤ q)
    (he : orderOf (q : ZMod p) = e) (hi : i ∈ e.properDivisors) :
    ¬ (p : ℤ) ∣ (cyclotomic i ℤ).eval (q : ℤ) := by
  intro h
  obtain ⟨hid, hie⟩ := Nat.mem_properDivisors.1 hi
  have hdvd : (cyclotomic i ℤ).eval (q : ℤ) ∣ (q : ℤ) ^ i - 1 := by
    have := eval_dvd (x := (q : ℤ)) (cyclotomic.dvd_X_pow_sub_one i ℤ)
    simpa using this
  have h2 : (p : ℤ) ∣ ((q ^ i - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]
    simpa using h.trans hdvd
  have h3 : p ∣ q ^ i - 1 := Int.natCast_dvd_natCast.1 h2
  have h4 := (dvd_pow_sub_one_iff_orderOf hq he).1 h3
  have h5 : 0 < i := Nat.pos_of_dvd_of_pos hid (by
    rcases Nat.eq_zero_or_pos e with rfl | h0
    · simp at hie
    · exact h0)
  have h6 := Nat.le_of_dvd h5 h4
  have h7 := Nat.le_of_dvd (by omega) hid
  omega

theorem ordProj_cyclotomic_eval {p q e : ℕ} (hp : p.Prime) (hq : 2 ≤ q)
    (he : orderOf (q : ZMod p) = e) (he0 : e ≠ 0) :
    p ^ ((cyclotomic e ℤ).eval (q : ℤ)).natAbs.factorization p =
      p ^ (q ^ e - 1).factorization p := by
  have hprod : ∏ i ∈ e.divisors, (cyclotomic i ℤ).eval (q : ℤ) = (q : ℤ) ^ e - 1 := by
    have := congrArg (eval (q : ℤ)) (prod_cyclotomic_eq_X_pow_sub_one (Nat.pos_of_ne_zero he0) ℤ)
    simpa [eval_prod] using this
  rw [← Nat.cons_self_properDivisors he0, Finset.prod_cons] at hprod
  set S : ℤ := ∏ i ∈ e.properDivisors, (cyclotomic i ℤ).eval (q : ℤ) with hS
  have hSp : ¬ (p : ℤ) ∣ S := by
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    rw [hS, hpz.dvd_finsetProd_iff]
    rintro ⟨i, hi, h⟩
    exact not_dvd_cyclotomic_eval_of_properDivisor (by omega) he hi h
  have hN : (q ^ e - 1 : ℕ) = ((cyclotomic e ℤ).eval (q : ℤ)).natAbs * S.natAbs := by
    have h1 : ((q ^ e - 1 : ℕ) : ℤ) = (cyclotomic e ℤ).eval (q : ℤ) * S := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), hprod]
      simp
    have := congrArg Int.natAbs h1
    simpa [Int.natAbs_mul] using this
  have hN0 : q ^ e - 1 ≠ 0 := by
    have : 1 < q ^ e := Nat.one_lt_pow he0 (by omega)
    omega
  have hn1 : ((cyclotomic e ℤ).eval (q : ℤ)).natAbs ≠ 0 := fun h => hN0 (by rw [hN, h, zero_mul])
  have hs : S.natAbs ≠ 0 := fun h => hN0 (by rw [hN, h, mul_zero])
  have hSp' : ¬ p ∣ S.natAbs := fun h => hSp (Int.natCast_dvd.2 h)
  conv_rhs => rw [hN]
  rw [Nat.ordProj_mul p hn1 hs, ordProj_eq_one_of_not_dvd' hSp', mul_one]

theorem ordProj_cyclotomic_pow_mul_eval {p q e m : ℕ} (hp : p.Prime) (hq : 2 ≤ q)
    (he : orderOf (q : ZMod p) = e) (he0 : e ≠ 0) {R : ℤ[X]} (hR : ¬ (p : ℤ) ∣ R.eval (q : ℤ)) :
    p ^ ((cyclotomic e ℤ ^ m * R).eval (q : ℤ)).natAbs.factorization p =
      (p ^ (q ^ e - 1).factorization p) ^ m := by
  have hpos : 0 < (cyclotomic e ℤ).eval (q : ℤ) := cyclotomic_pos' e (by exact_mod_cast hq)
  have hΦ : ((cyclotomic e ℤ).eval (q : ℤ)).natAbs ≠ 0 := Int.natAbs_ne_zero.2 hpos.ne'
  have hR0 : (R.eval (q : ℤ)).natAbs ≠ 0 := fun h => hR (by
    rw [Int.natAbs_eq_zero.1 h]
    exact dvd_zero _)
  rw [eval_mul, eval_pow, Int.natAbs_mul, Int.natAbs_pow, Nat.ordProj_mul p (pow_ne_zero m hΦ) hR0,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, pow_mul', ← ordProj_cyclotomic_eval hp
      hq he he0, ordProj_eq_one_of_not_dvd' (fun h => hR (Int.natCast_dvd.2 h)), mul_one]

theorem prod_ordProj_pow_sub_one {p q e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ q)
    (hq : 2 ≤ q) (he : orderOf (q : ZMod p) = e) (D : List ℕ)
    (hD : ∀ d ∈ D, e ∣ d → d ≠ 0 ∧ ¬ p ∣ d / e) :
    (D.map fun d => p ^ (q ^ d - 1).factorization p).prod =
      (p ^ (q ^ e - 1).factorization p) ^ (D.filter fun d => e ∣ d).length := by
  induction D with
  | nil => simp
  | cons d D ih =>
    have ih' := ih fun d' hd' => hD d' (List.mem_cons_of_mem _ hd')
    rw [List.map_cons, List.prod_cons, ih']
    by_cases hed : e ∣ d
    · obtain ⟨hd0, hpd⟩ := hD d List.mem_cons_self hed
      obtain ⟨k, rfl⟩ := hed
      have he0 : e ≠ 0 := fun h => hd0 (by rw [h, zero_mul])
      have hk : k ≠ 0 := fun h => hd0 (by rw [h, mul_zero])
      have hk1 : p ^ k.factorization p = 1 := ordProj_eq_one_of_not_dvd' (by
        simpa [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he0)] using hpd)
      rw [ordProj_pow_sub_one_of_dvd hp hp2 hpq hq he hk, hk1, mul_one,
        List.filter_cons_of_pos (by simp), List.length_cons, pow_succ,
        mul_comm]
    · rw [ordProj_pow_sub_one_of_not_dvd (by omega) he hed, one_mul,
        List.filter_cons_of_neg (by simpa using hed)]

end CFSG.LieType.SeitzGeneration
