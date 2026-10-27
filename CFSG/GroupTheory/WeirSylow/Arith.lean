module

public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.GroupTheory.WeirSylow

open Finset

noncomputable abbrev ordMod (p : ℕ) (c : ℤ) : ℕ :=
  orderOf (c : ZMod p)

theorem ordMod_natCast (p q : ℕ) : ordMod p (q : ℤ) = orderOf (q : ZMod p) :=
  congrArg orderOf (Int.cast_natCast q)

theorem sum_Icc_ite_dvd (p : ℕ) [hp : Fact p.Prime] {e : ℕ} (he : 0 < e) (a : ℕ) :
    ∀ n : ℕ, ∑ j ∈ Icc 1 n, (if e ∣ j then a + padicValNat p (j / e) else 0) =
      a * (n / e) + padicValNat p (n / e).factorial
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_Icc_succ_top (by omega), sum_Icc_ite_dvd p he a n]
    split_ifs with hdvd
    · obtain ⟨k, hk⟩ := hdvd
      have hk0 : k ≠ 0 := by
        rintro rfl
        simp at hk
      have h1 : (n + 1) / e = k := by rw [hk, Nat.mul_div_cancel_left _ he]
      have h2 : n / e = k - 1 := by
        rw [Nat.succ_div_of_dvd ⟨k, hk⟩] at h1
        omega
      rw [h1, h2, ← Nat.mul_factorial_pred hk0,
        padicValNat.mul hk0 (Nat.factorial_ne_zero _)]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    · rw [Nat.succ_div_of_not_dvd hdvd, add_zero]

variable {p : ℕ} [hp : Fact p.Prime]

theorem padicValInt_cast_eq_emultiplicity {z : ℤ} (hz : z ≠ 0) :
    (padicValInt p z : ℕ∞) = emultiplicity (p : ℤ) z := by
  rw [padicValInt, padicValNat_eq_emultiplicity (Int.natAbs_ne_zero.2 hz),
    Int.emultiplicity_natAbs]

theorem two_le_abs_of_dvd_sub_one (hp1 : Odd p) {x : ℤ} (hx1 : x ≠ 1)
    (hxy : (p : ℤ) ∣ x - 1) : 2 ≤ |x| := by
  by_contra h
  have h' : x = -1 ∨ x = 0 := by
    have := abs_lt.1 (show |x| < 2 by omega)
    omega
  have hp2 := hp.out.two_le
  rcases h' with rfl | rfl
  · have h2 : (p : ℤ) ∣ 2 := by
      have := dvd_neg.2 hxy
      norm_num at this
      exact this
    have h3 : p ≤ 2 := by exact_mod_cast Int.le_of_dvd (by norm_num) h2
    have : p = 2 := by omega
    exact (Nat.not_even_iff_odd.2 hp1) (this ▸ even_two)
  · have h2 : (p : ℤ) ∣ 1 := by simpa using hxy
    have h3 : p = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h2
    omega

theorem pow_sub_one_ne_zero {x : ℤ} (hx : 2 ≤ |x|) {k : ℕ} (hk : k ≠ 0) : x ^ k - 1 ≠ 0 := by
  intro h
  have h1 : |x| ^ k = 1 := by rw [← abs_pow, sub_eq_zero.1 h, abs_one]
  have h2 : 2 ^ k ≤ |x| ^ k := pow_le_pow_left₀ (by norm_num) hx k
  have h3 : (2 : ℤ) ^ 1 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (Nat.one_le_iff_ne_zero.2 hk)
  omega

theorem padicValInt_pow_sub_one (hp1 : Odd p) {x : ℤ} (hx1 : x ≠ 1) (hxy : (p : ℤ) ∣ x - 1)
    (hx : ¬ (p : ℤ) ∣ x) {k : ℕ} (hk : k ≠ 0) :
    padicValInt p (x ^ k - 1) = padicValInt p (x - 1) + padicValNat p k := by
  have h2 := two_le_abs_of_dvd_sub_one hp1 hx1 hxy
  have h := Int.emultiplicity_pow_sub_pow hp.out hp1 (y := 1) (by simpa using hxy) hx k
  rw [one_pow, ← padicValInt_cast_eq_emultiplicity (pow_sub_one_ne_zero h2 hk),
    ← padicValInt_cast_eq_emultiplicity (sub_ne_zero.2 hx1),
    ← padicValNat_eq_emultiplicity hk] at h
  exact_mod_cast h

theorem intCast_ne_zero_of_not_dvd {c : ℤ} (hc : ¬ (p : ℤ) ∣ c) : (c : ZMod p) ≠ 0 := by
  rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem ordMod_pos {c : ℤ} (hc : ¬ (p : ℤ) ∣ c) : 0 < ordMod p c :=
  orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p - 1, by
    have := hp.out.one_lt
    omega, ZMod.pow_card_sub_one_eq_one (intCast_ne_zero_of_not_dvd hc)⟩)

theorem dvd_pow_sub_one_iff {c : ℤ} (j : ℕ) :
    (p : ℤ) ∣ c ^ j - 1 ↔ ordMod p c ∣ j := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_pow, Int.cast_one,
    sub_eq_zero, orderOf_dvd_iff_pow_eq_one]

theorem pow_ordMod_ne_one {c : ℤ} (hc : ¬ (p : ℤ) ∣ c) (hc2 : 2 ≤ |c|) :
    c ^ ordMod p c ≠ 1 := fun h =>
  pow_sub_one_ne_zero hc2 (ordMod_pos hc).ne' (by rw [h, sub_self])

theorem padicValInt_pow_sub_one_eq (hp1 : Odd p) {c : ℤ} (hc : ¬ (p : ℤ) ∣ c)
    (hc2 : 2 ≤ |c|) {j : ℕ} (hj : j ≠ 0) :
    padicValInt p (c ^ j - 1) = if ordMod p c ∣ j then
      padicValInt p (c ^ ordMod p c - 1) + padicValNat p (j / ordMod p c) else 0 := by
  have he := ordMod_pos hc
  split_ifs with hdvd
  · obtain ⟨k, rfl⟩ := hdvd
    have hk : k ≠ 0 := by
      rintro rfl
      exact hj (mul_zero _)
    rw [Nat.mul_div_cancel_left _ he, pow_mul]
    refine padicValInt_pow_sub_one hp1 (pow_ordMod_ne_one hc hc2)
      ((dvd_pow_sub_one_iff _).2 dvd_rfl) (fun h => ?_) hk
    exact hc ((Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow h)
  · exact padicValInt.eq_zero_of_not_dvd (by rwa [dvd_pow_sub_one_iff])

theorem sum_padicValInt_pow_sub_one (hp1 : Odd p) {c : ℤ} (hc : ¬ (p : ℤ) ∣ c)
    (hc2 : 2 ≤ |c|) (n : ℕ) : ∑ j ∈ Icc 1 n, padicValInt p (c ^ j - 1) =
      padicValInt p (c ^ ordMod p c - 1) * (n / ordMod p c) +
        padicValNat p (n / ordMod p c).factorial := by
  rw [← sum_Icc_ite_dvd p (ordMod_pos hc)]
  refine Finset.sum_congr rfl fun j hj => ?_
  exact padicValInt_pow_sub_one_eq hp1 hc hc2 (by have := (mem_Icc.1 hj).1; omega)

theorem padicValInt_prod {s : Finset ℕ} {f : ℕ → ℤ} (hf : ∀ j ∈ s, f j ≠ 0) :
    padicValInt p (∏ j ∈ s, f j) = ∑ j ∈ s, padicValInt p (f j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, sum_insert hj, padicValInt.mul (hf j (mem_insert_self j s))
      (prod_ne_zero_iff.2 fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

theorem factorization_eq_padicValInt {N : ℕ} : N.factorization p = padicValInt p N := by
  rw [Nat.factorization_def N hp.out, padicValInt.of_nat]

theorem factorization_eq_of_cast_eq_mul_prod (hp1 : Odd p) {c : ℤ} (hc : ¬ (p : ℤ) ∣ c)
    (hc2 : 2 ≤ |c|) {N : ℕ} {u : ℤ} {n : ℕ} (hN : (N : ℤ) = u * ∏ j ∈ Icc 1 n, (c ^ j - 1))
    (hu : ¬ (p : ℤ) ∣ u) : N.factorization p =
      padicValInt p (c ^ ordMod p c - 1) * (n / ordMod p c) +
        padicValNat p (n / ordMod p c).factorial := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hu (dvd_zero _)
  have hne : ∀ j ∈ Icc 1 n, c ^ j - 1 ≠ 0 := fun j hj =>
    pow_sub_one_ne_zero hc2 (by have := (mem_Icc.1 hj).1; omega)
  rw [factorization_eq_padicValInt, hN, padicValInt.mul hu0 (prod_ne_zero_iff.2 hne),
    padicValInt.eq_zero_of_not_dvd hu, zero_add, padicValInt_prod hne,
    sum_padicValInt_pow_sub_one hp1 hc hc2]

theorem ordMod_sq (c : ℤ) :
    ordMod p (c ^ 2) = if Even (ordMod p c) then ordMod p c / 2 else ordMod p c := by
  rw [ordMod, Int.cast_pow, orderOf_pow' _ two_ne_zero]
  split_ifs with he
  · rw [Nat.gcd_eq_right (even_iff_two_dvd.1 he)]
  · rw [(Nat.coprime_two_right.2 (Nat.not_even_iff_odd.1 he)).gcd_eq_one, Nat.div_one]

theorem not_dvd_pow_ordMod_add_one (hp1 : Odd p) (c : ℤ) : ¬ (p : ℤ) ∣ c ^ ordMod p c + 1 := by
  intro h
  have h1 : (p : ℤ) ∣ c ^ ordMod p c - 1 := (dvd_pow_sub_one_iff _).2 dvd_rfl
  have h2 : (p : ℤ) ∣ 2 := by
    have := dvd_sub h h1
    rwa [show c ^ ordMod p c + 1 - (c ^ ordMod p c - 1) = 2 by ring] at this
  have h3 : p ≤ 2 := by exact_mod_cast Int.le_of_dvd (by norm_num) h2
  have := hp.out.two_le
  have : p = 2 := by omega
  exact (Nat.not_even_iff_odd.2 hp1) (this ▸ even_two)

theorem padicValInt_sq_pow_ordMod_sub_one (hp1 : Odd p) (c : ℤ) :
    padicValInt p ((c ^ 2) ^ ordMod p (c ^ 2) - 1) = padicValInt p (c ^ ordMod p c - 1) := by
  rw [ordMod_sq]
  split_ifs with he
  · rw [← pow_mul, Nat.mul_div_cancel' (even_iff_two_dvd.1 he)]
  · have hfac : (c ^ 2) ^ ordMod p c - 1 = (c ^ ordMod p c - 1) * (c ^ ordMod p c + 1) := by
      ring
    by_cases h0 : c ^ ordMod p c - 1 = 0
    · rw [hfac, h0, zero_mul]
    have h1 : c ^ ordMod p c + 1 ≠ 0 := fun h =>
      not_dvd_pow_ordMod_add_one hp1 c (h ▸ dvd_zero _)
    rw [hfac, padicValInt.mul h0 h1,
      padicValInt.eq_zero_of_not_dvd (not_dvd_pow_ordMod_add_one hp1 c), add_zero]

theorem padicValInt_sub_eq_sq_sub_one {x ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (h : ¬ (p : ℤ) ∣ x + ε) : padicValInt p (x - ε) = padicValInt p (x ^ 2 - 1) := by
  have hfac : x ^ 2 - 1 = (x - ε) * (x + ε) := by
    rcases hε with rfl | rfl <;> ring
  have h1 : x + ε ≠ 0 := fun h' => h (h' ▸ dvd_zero _)
  by_cases h0 : x - ε = 0
  · rw [hfac, h0, zero_mul]
  rw [hfac, padicValInt.mul h0 h1, padicValInt.eq_zero_of_not_dvd h, add_zero]

theorem not_dvd_add_one_or_not_dvd_sub_one (hp1 : Odd p) (x : ℤ) :
    ¬ (p : ℤ) ∣ x + 1 ∨ ¬ (p : ℤ) ∣ x - 1 := by
  by_contra! h
  have h2 : (p : ℤ) ∣ 2 := by
    have := dvd_sub h.1 h.2
    rwa [show x + 1 - (x - 1) = 2 by ring] at this
  have h3 : p ≤ 2 := by exact_mod_cast Int.le_of_dvd (by norm_num) h2
  have := hp.out.two_le
  have : p = 2 := by omega
  exact (Nat.not_even_iff_odd.2 hp1) (this ▸ even_two)

end CFSG.GroupTheory.WeirSylow
