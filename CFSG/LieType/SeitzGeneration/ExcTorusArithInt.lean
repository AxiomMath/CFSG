module

public import CFSG.LieType.SeitzGeneration.ExcTorusArith

public section

namespace CFSG.LieType.SeitzGeneration

open Polynomial

theorem dvd_int_pow_sub_one_iff_orderOf {p e d : ℕ} {Q : ℤ} (he : orderOf (Q : ZMod p) = e) :
    (p : ℤ) ∣ Q ^ d - 1 ↔ e ∣ d := by
  rw [← he, orderOf_dvd_iff_pow_eq_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact sub_eq_zero

theorem ordProj_int_pow_sub_one_of_not_dvd {p e d : ℕ} {Q : ℤ}
    (he : orderOf (Q : ZMod p) = e) (hd : ¬ e ∣ d) :
    p ^ ((Q ^ d - 1).natAbs).factorization p = 1 :=
  ordProj_eq_one_of_not_dvd' fun h =>
    hd ((dvd_int_pow_sub_one_iff_orderOf he).1 (Int.natCast_dvd.2 h))

theorem int_pow_sub_one_ne_zero {Q : ℤ} (hQ : 2 ≤ Q.natAbs) {d : ℕ} (hd : d ≠ 0) :
    Q ^ d - 1 ≠ 0 := by
  intro h
  have h1 : Q ^ d = 1 := sub_eq_zero.1 h
  have h2 : Q.natAbs ^ d = 1 := by
    have := congrArg Int.natAbs h1
    simpa [Int.natAbs_pow] using this
  have h3 : 1 < Q.natAbs ^ d := Nat.one_lt_pow hd (by omega)
  omega

theorem ordProj_int_pow_sub_one_of_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : ℤ} {e k : ℕ}
    (hQ : 2 ≤ Q.natAbs) (hpQ : ¬ (p : ℤ) ∣ Q) (he : orderOf (Q : ZMod p) = e) (he0 : e ≠ 0)
    (hk : k ≠ 0) :
    p ^ ((Q ^ (e * k) - 1).natAbs).factorization p =
      p ^ ((Q ^ e - 1).natAbs).factorization p * p ^ k.factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : (p : ℤ) ∣ Q ^ e - 1 := (dvd_int_pow_sub_one_iff_orderOf he).2 dvd_rfl
  have hpQe : ¬ (p : ℤ) ∣ Q ^ e := fun h =>
    hpQ ((Nat.prime_iff_prime_int.1 hp).dvd_of_dvd_pow h)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have h := Int.emultiplicity_pow_sub_pow hp hodd (x := Q ^ e) (y := 1) hdvd hpQe k
  rw [one_pow, ← pow_mul] at h
  have hz1 : (Q ^ (e * k) - 1).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.2 (int_pow_sub_one_ne_zero hQ (mul_ne_zero he0 hk))
  have hz2 : (Q ^ e - 1).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (int_pow_sub_one_ne_zero hQ he0)
  rw [← Int.emultiplicity_natAbs, ← Int.emultiplicity_natAbs,
    ← padicValNat_eq_emultiplicity hz1, ← padicValNat_eq_emultiplicity hz2,
    ← padicValNat_eq_emultiplicity hk] at h
  have h' : padicValNat p (Q ^ (e * k) - 1).natAbs =
      padicValNat p (Q ^ e - 1).natAbs + padicValNat p k := by exact_mod_cast h
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, Nat.factorization_def _ hp, h',
    pow_add]

theorem not_dvd_cyclotomic_int_eval_of_properDivisor {p e i : ℕ} {Q : ℤ}
    (he : orderOf (Q : ZMod p) = e) (hi : i ∈ e.properDivisors) :
    ¬ (p : ℤ) ∣ (cyclotomic i ℤ).eval Q := by
  intro h
  obtain ⟨hid, hie⟩ := Nat.mem_properDivisors.1 hi
  have hdvd : (cyclotomic i ℤ).eval Q ∣ Q ^ i - 1 := by
    have := eval_dvd (x := Q) (cyclotomic.dvd_X_pow_sub_one i ℤ)
    simpa using this
  have h4 := (dvd_int_pow_sub_one_iff_orderOf he).1 (h.trans hdvd)
  have h5 : 0 < i := Nat.pos_of_dvd_of_pos hid (by
    rcases Nat.eq_zero_or_pos e with rfl | h0
    · simp at hie
    · exact h0)
  have h6 := Nat.le_of_dvd h5 h4
  have h7 := Nat.le_of_dvd (by omega) hid
  omega

theorem ordProj_cyclotomic_int_eval {p e : ℕ} {Q : ℤ} (hp : p.Prime) (hQ : 2 ≤ Q.natAbs)
    (he : orderOf (Q : ZMod p) = e) (he0 : e ≠ 0) :
    p ^ ((cyclotomic e ℤ).eval Q).natAbs.factorization p =
      p ^ ((Q ^ e - 1).natAbs).factorization p := by
  have hprod : ∏ i ∈ e.divisors, (cyclotomic i ℤ).eval Q = Q ^ e - 1 := by
    have := congrArg (eval Q) (prod_cyclotomic_eq_X_pow_sub_one (Nat.pos_of_ne_zero he0) ℤ)
    simpa [eval_prod] using this
  rw [← Nat.cons_self_properDivisors he0, Finset.prod_cons] at hprod
  set S : ℤ := ∏ i ∈ e.properDivisors, (cyclotomic i ℤ).eval Q with hS
  have hSp : ¬ (p : ℤ) ∣ S := by
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    rw [hS, hpz.dvd_finsetProd_iff]
    rintro ⟨i, hi, h⟩
    exact not_dvd_cyclotomic_int_eval_of_properDivisor he hi h
  have hN : (Q ^ e - 1).natAbs = ((cyclotomic e ℤ).eval Q).natAbs * S.natAbs := by
    have := congrArg Int.natAbs hprod
    simpa [Int.natAbs_mul] using this.symm
  have hN0 : (Q ^ e - 1).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (int_pow_sub_one_ne_zero hQ he0)
  have hn1 : ((cyclotomic e ℤ).eval Q).natAbs ≠ 0 := fun h => hN0 (by rw [hN, h, zero_mul])
  have hs : S.natAbs ≠ 0 := fun h => hN0 (by rw [hN, h, mul_zero])
  have hSp' : ¬ p ∣ S.natAbs := fun h => hSp (Int.natCast_dvd.2 h)
  conv_rhs => rw [hN]
  rw [Nat.ordProj_mul p hn1 hs, ordProj_eq_one_of_not_dvd' hSp', mul_one]

theorem prod_ordProj_int_pow_sub_one {p : ℕ} {Q : ℤ} {e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : 2 ≤ Q.natAbs) (hpQ : ¬ (p : ℤ) ∣ Q) (he : orderOf (Q : ZMod p) = e) (D : List ℕ)
    (hD : ∀ d ∈ D, e ∣ d → d ≠ 0 ∧ ¬ p ∣ d / e) :
    (D.map fun d => p ^ ((Q ^ d - 1).natAbs).factorization p).prod =
      (p ^ ((Q ^ e - 1).natAbs).factorization p) ^ (D.filter fun d => e ∣ d).length := by
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
      rw [ordProj_int_pow_sub_one_of_dvd hp hp2 hQ hpQ he he0 hk, hk1, mul_one,
        List.filter_cons_of_pos (by simp), List.length_cons, pow_succ, mul_comm]
    · rw [ordProj_int_pow_sub_one_of_not_dvd he hed, one_mul,
        List.filter_cons_of_neg (by simpa using hed)]

end CFSG.LieType.SeitzGeneration
