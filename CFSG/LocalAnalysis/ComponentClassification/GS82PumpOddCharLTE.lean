module

public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.OddChar

open Finset

@[expose] def fac (Q : ℤ) (d : ℕ) : ℕ := (Q ^ d - 1).natAbs

@[expose] noncomputable def ord (s : ℕ) (Q : ℤ) : ℕ := orderOf (Q : ZMod s)

structure Setup (s q : ℕ) (Q : ℤ) : Prop where
  prime : s.Prime
  odd_s : Odd s
  natAbs_eq : Q.natAbs = q
  three_le : 3 ≤ q
  odd_q : Odd q
  not_dvd : ¬ s ∣ q

theorem ordProj_lt_of_even {s x : ℕ} (hs : Odd s) (hx : x ≠ 0) (he : Even x) :
    ordProj[s] x < x := by
  refine lt_of_le_of_ne (Nat.ordProj_le s hx) fun heq => ?_
  have ho : Odd (ordProj[s] x) := hs.pow
  rw [heq] at ho
  exact Nat.not_even_iff_odd.mpr ho he

theorem ordProj_prod {ι : Type*} {S : Finset ι} {g : ι → ℕ} (hg : ∀ i ∈ S, g i ≠ 0) (s : ℕ) :
    ordProj[s] (∏ i ∈ S, g i) = ∏ i ∈ S, ordProj[s] (g i) := by
  rw [Nat.factorization_prod hg, Finsupp.finset_sum_apply, Finset.prod_pow_eq_pow_sum]

theorem le_pow_sub_two {q m : ℕ} (hq : 3 ≤ q) (hm : 3 ≤ m) : m ≤ q ^ (m - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  rw [show k + 3 - 2 = k + 1 by omega, pow_succ]
  have hk : k < q ^ k := Nat.lt_pow_self (by omega)
  calc k + 3 ≤ (k + 1) * 3 := by omega
    _ ≤ q ^ k * q := Nat.mul_le_mul hk hq

namespace Setup

variable {s q : ℕ} {Q : ℤ}

theorem odd_Q (h : Setup s q Q) : Odd Q := by
  rw [← Int.natAbs_odd, h.natAbs_eq]
  exact h.odd_q

theorem not_dvd_Q (h : Setup s q Q) : ¬ (s : ℤ) ∣ Q := by
  rw [Int.ofNat_dvd_left, h.natAbs_eq]
  exact h.not_dvd

theorem ord_pos (h : Setup s q Q) : 0 < ord s Q := by
  have : Fact s.Prime := ⟨h.prime⟩
  have hQ : (Q : ZMod s) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h.not_dvd_Q
  exact Nat.pos_of_dvd_of_pos (ZMod.orderOf_dvd_card_sub_one hQ)
    (by have := h.prime.two_le; omega)

theorem dvd_fac_iff (h : Setup s q Q) (d : ℕ) : s ∣ fac Q d ↔ ord s Q ∣ d := by
  rw [fac, ← Int.ofNat_dvd_left, ← ZMod.intCast_zmod_eq_zero_iff_dvd, ord,
    orderOf_dvd_iff_pow_eq_one]
  push_cast
  rw [sub_eq_zero]

theorem factorization_fac_eq_zero (h : Setup s q Q) {d : ℕ} (hd : ¬ ord s Q ∣ d) :
    (fac Q d).factorization s = 0 :=
  Nat.factorization_eq_zero_of_not_dvd fun hs => hd ((h.dvd_fac_iff d).mp hs)

theorem fac_ne_zero (h : Setup s q Q) {d : ℕ} (hd : d ≠ 0) : fac Q d ≠ 0 := by
  rw [fac, Int.natAbs_ne_zero, sub_ne_zero]
  intro h1
  have h2 := congrArg Int.natAbs h1
  rw [Int.natAbs_pow, h.natAbs_eq, Int.natAbs_one] at h2
  have : 1 < q ^ d := Nat.one_lt_pow hd (by have := h.three_le; omega)
  omega

theorem even_fac (h : Setup s q Q) (d : ℕ) : Even (fac Q d) := by
  rw [fac, Int.natAbs_even]
  exact h.odd_Q.pow.sub_odd odd_one

theorem fac_le (h : Setup s q Q) (d : ℕ) : fac Q d ≤ q ^ d + 1 := by
  have h1 := Int.natAbs_sub_le (Q ^ d) 1
  rwa [Int.natAbs_pow, h.natAbs_eq, Int.natAbs_one] at h1

theorem ordProj_fac_le (h : Setup s q Q) {d : ℕ} (hd : d ≠ 0) : ordProj[s] (fac Q d) ≤ q ^ d := by
  have h1 := ordProj_lt_of_even h.odd_s (h.fac_ne_zero hd) (h.even_fac d)
  have h2 := h.fac_le d
  omega

theorem factorization_fac_cast (h : Setup s q Q) {d : ℕ} (hd : d ≠ 0) :
    ((fac Q d).factorization s : ℕ∞) = emultiplicity (s : ℤ) (Q ^ d - 1) := by
  have : Fact s.Prime := ⟨h.prime⟩
  rw [Nat.factorization_def _ h.prime, padicValNat_eq_emultiplicity (h.fac_ne_zero hd), fac,
    Int.emultiplicity_natAbs]

theorem ordProj_fac_ord_mul (h : Setup s q Q) {m : ℕ} (hm : m ≠ 0) :
    ordProj[s] (fac Q (ord s Q * m)) = ordProj[s] (fac Q (ord s Q)) * ordProj[s] m := by
  have : Fact s.Prime := ⟨h.prime⟩
  have he := h.ord_pos
  have hdvd : (s : ℤ) ∣ Q ^ ord s Q - 1 := by
    rw [Int.ofNat_dvd_left]
    exact (h.dvd_fac_iff _).mpr dvd_rfl
  have hx : ¬ (s : ℤ) ∣ Q ^ ord s Q := fun hs =>
    h.not_dvd_Q ((Nat.prime_iff_prime_int.mp h.prime).dvd_of_dvd_pow hs)
  have key := Int.emultiplicity_pow_sub_pow h.prime h.odd_s (x := Q ^ ord s Q) (y := 1) hdvd hx m
  rw [one_pow] at key
  have e3 : (m.factorization s : ℕ∞) = emultiplicity s m := by
    rw [Nat.factorization_def _ h.prime, padicValNat_eq_emultiplicity hm]
  have hval : ((fac Q (ord s Q * m)).factorization s : ℕ∞) =
      ((fac Q (ord s Q)).factorization s : ℕ∞) + (m.factorization s : ℕ∞) := by
    rw [h.factorization_fac_cast (Nat.mul_ne_zero he.ne' hm), h.factorization_fac_cast he.ne', e3,
      pow_mul, key]
  have hval' : (fac Q (ord s Q * m)).factorization s =
      (fac Q (ord s Q)).factorization s + m.factorization s := by
    exact_mod_cast hval
  rw [hval', pow_add]

theorem ordProj_fac_ord_le_half (h : Setup s q Q) {k : ℕ} (hk : ord s Q = 2 * k) :
    ordProj[s] (fac Q (ord s Q)) ≤ q ^ k := by
  have he := h.ord_pos
  have hk0 : k ≠ 0 := by omega
  have hsplit : fac Q (ord s Q) = fac Q k * (Q ^ k + 1).natAbs := by
    rw [fac, fac, hk, ← Int.natAbs_mul]
    congr 1
    ring
  have hne2 : (Q ^ k + 1).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    intro h0
    have h1 := congrArg Int.natAbs (eq_neg_of_add_eq_zero_left h0)
    rw [Int.natAbs_pow, h.natAbs_eq, Int.natAbs_neg, Int.natAbs_one] at h1
    have : 1 < q ^ k := Nat.one_lt_pow hk0 (by have := h.three_le; omega)
    omega
  have hnd : ¬ ord s Q ∣ k := fun hd => by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hd
    omega
  rw [hsplit, Nat.ordProj_mul s (h.fac_ne_zero hk0) hne2, h.factorization_fac_eq_zero hnd,
    pow_zero, one_mul]
  have hev : Even (Q ^ k + 1).natAbs := by
    rw [Int.natAbs_even]
    exact h.odd_Q.pow.add_odd odd_one
  have hle : (Q ^ k + 1).natAbs ≤ q ^ k + 1 := by
    have h1 := Int.natAbs_add_le (Q ^ k) 1
    rwa [Int.natAbs_pow, h.natAbs_eq, Int.natAbs_one] at h1
  have := ordProj_lt_of_even h.odd_s hne2 hev
  omega

theorem ordProj_fac_ord_mul_le (h : Setup s q Q) {m E : ℕ} (hm : 3 ≤ m) (hE1 : 1 ≤ E)
    (hE : ordProj[s] (fac Q (ord s Q)) ≤ q ^ E) :
    ordProj[s] (fac Q (ord s Q * m)) ≤ q ^ (E * m - 1) := by
  rw [h.ordProj_fac_ord_mul (by omega)]
  have h1 : ordProj[s] m ≤ m := Nat.ordProj_le s (by omega)
  have h2 : m ≤ q ^ (m - 2) := le_pow_sub_two h.three_le hm
  have h4 : E + m ≤ E * m + 1 := by nlinarith
  calc ordProj[s] (fac Q (ord s Q)) * ordProj[s] m ≤ q ^ E * q ^ (m - 2) :=
        Nat.mul_le_mul hE (h1.trans h2)
    _ = q ^ (E + (m - 2)) := (pow_add _ _ _).symm
    _ ≤ q ^ (E * m - 1) := Nat.pow_le_pow_right (by have := h.three_le; omega) (by omega)

theorem not_dvd_two (h : Setup s q Q) : ¬ s ∣ 2 := fun hs => by
  have h2 := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp hs
  have := h.odd_s
  rw [h2] at this
  exact absurd this (by decide)

theorem ordProj_fac_le_pred (h : Setup s q Q) {d : ℕ} (hd : 2 ≤ d)
    (hne : ¬ (d = ord s Q ∧ Odd (ord s Q))) : ordProj[s] (fac Q d) ≤ q ^ (d - 1) := by
  have hq1 : 0 < q := by have := h.three_le; omega
  by_cases hed : ord s Q ∣ d
  · obtain ⟨m, rfl⟩ := hed
    have he := h.ord_pos
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hd
    rcases (show m = 1 ∨ m = 2 ∨ 3 ≤ m by omega) with rfl | rfl | hm
    · rw [mul_one] at hne ⊢
      have hev : Even (ord s Q) := by
        rcases Nat.even_or_odd (ord s Q) with h' | h'
        · exact h'
        · exact absurd ⟨rfl, h'⟩ hne
      obtain ⟨k, hk⟩ := hev
      calc ordProj[s] (fac Q (ord s Q)) ≤ q ^ k := h.ordProj_fac_ord_le_half (by omega)
        _ ≤ q ^ (ord s Q - 1) := Nat.pow_le_pow_right hq1 (by omega)
    · rw [h.ordProj_fac_ord_mul two_ne_zero, Nat.factorization_eq_zero_of_not_dvd h.not_dvd_two,
        pow_zero, mul_one]
      calc ordProj[s] (fac Q (ord s Q)) ≤ q ^ ord s Q := h.ordProj_fac_le he.ne'
        _ ≤ q ^ (ord s Q * 2 - 1) := Nat.pow_le_pow_right hq1 (by omega)
    · exact h.ordProj_fac_ord_mul_le hm he (h.ordProj_fac_le he.ne')
  · rw [h.factorization_fac_eq_zero hed, pow_zero]
    exact Nat.one_le_pow _ _ hq1

theorem prod_ordProj_fac_le (h : Setup s q Q) {ι : Type*} [DecidableEq ι] {S : Finset ι}
    {deg : ι → ℕ} (hdeg : ∀ i ∈ S, 2 ≤ deg i) {i₂ : ι} (hi₂ : i₂ ∈ S) (hdeg₂ : deg i₂ = 2)
    (hodd : ∀ i ∈ S, ∀ j ∈ S, deg i = deg j → Odd (deg i) → i = j) :
    ∏ i ∈ S, ordProj[s] (fac Q (deg i)) ≤ q ^ ∑ i ∈ S, (deg i - 1) := by
  by_cases hj : ∃ j ∈ S, deg j = ord s Q ∧ Odd (ord s Q)
  · obtain ⟨j, hjS, hje, hodde⟩ := hj
    have hj3 : 3 ≤ deg j := by
      have := hdeg j hjS
      rw [hje] at this ⊢
      obtain ⟨k, hk⟩ := hodde
      omega
    have hj2 : j ≠ i₂ := by
      rintro rfl
      omega
    have hi₂' : i₂ ∈ S.erase j := Finset.mem_erase.mpr ⟨hj2.symm, hi₂⟩
    rw [← Finset.mul_prod_erase S _ hjS, ← Finset.mul_prod_erase (S.erase j) _ hi₂',
      ← Finset.add_sum_erase S _ hjS, ← Finset.add_sum_erase (S.erase j) _ hi₂']
    have h1 : ordProj[s] (fac Q (deg j)) ≤ q ^ deg j := h.ordProj_fac_le (by omega)
    have h2 : ordProj[s] (fac Q (deg i₂)) = 1 := by
      rw [h.factorization_fac_eq_zero, pow_zero]
      rw [hdeg₂, ← hje]
      intro hd
      have := Nat.le_of_dvd two_pos hd
      omega
    have h3 : ∏ i ∈ (S.erase j).erase i₂, ordProj[s] (fac Q (deg i)) ≤
        q ^ ∑ i ∈ (S.erase j).erase i₂, (deg i - 1) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod fun i hi => ?_
      have hi1 := Finset.mem_erase.mp hi
      have hi2 := Finset.mem_erase.mp hi1.2
      refine h.ordProj_fac_le_pred (hdeg i hi2.2) fun ⟨hie, hodd'⟩ => hi2.1 ?_
      exact hodd i hi2.2 j hjS (hie.trans hje.symm) (hie ▸ hodd')
    rw [h2, one_mul, hdeg₂]
    calc ordProj[s] (fac Q (deg j)) * ∏ i ∈ (S.erase j).erase i₂, ordProj[s] (fac Q (deg i))
        ≤ q ^ deg j * q ^ ∑ i ∈ (S.erase j).erase i₂, (deg i - 1) := Nat.mul_le_mul h1 h3
      _ = q ^ (deg j - 1 + (2 - 1 + ∑ i ∈ (S.erase j).erase i₂, (deg i - 1))) := by
        rw [← pow_add]
        congr 1
        omega
  · push Not at hj
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod fun i hi =>
      h.ordProj_fac_le_pred (hdeg i hi) fun ⟨h1, h2⟩ => hj i hi h1 h2

end Setup

end CFSG.ComponentClassification.GS82PumpInputs.OddChar
