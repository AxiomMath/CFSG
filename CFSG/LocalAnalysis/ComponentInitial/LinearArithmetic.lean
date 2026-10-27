module

public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Finset

theorem ordProj_two_eq (n : ℕ) : ordProj[2] n = 2 ^ padicValNat 2 n := by
  rw [Nat.factorization_def n Nat.prime_two]

theorem ordProj_two_pow_sq_sub_one {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    ordProj[2] ((p ^ f) ^ 2 - 1) = ordProj[2] (p ^ 2 - 1) * ordProj[2] f := by
  have hodd : ¬2 ∣ p := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
  have hA := padicValNat.pow_two_sub_one (n := 2 * f) hp.one_lt hodd (by omega) (even_two_mul f)
  have hB := padicValNat.pow_two_sub_one (n := 2) hp.one_lt hodd (by omega) even_two
  have h2f : padicValNat 2 (2 * f) = 1 + padicValNat 2 f := by
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
  rw [padicValNat.self (by norm_num)] at hB
  rw [ordProj_two_eq, ordProj_two_eq, ordProj_two_eq, ← pow_add, ← pow_mul, mul_comm f 2]
  congr 1
  omega

theorem eight_mul_ordProj_two_le {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    8 * ordProj[2] f ≤ ordProj[2] ((p ^ f) ^ 2 - 1) := by
  rw [ordProj_two_pow_sq_sub_one hp hp2 hf]
  refine Nat.mul_le_mul_right _ ?_
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have h1 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
  have h8 : 2 ^ 3 ∣ p ^ 2 - 1 := Nat.eight_dvd_sq_sub_one_of_odd hodd
  have h3 := (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mp h8
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ ordProj[2] (p ^ 2 - 1) := Nat.pow_le_pow_right (by norm_num) h3

theorem ordProj_two_sub_le_sub_pow {x y : ℤ} {j : ℕ} (h : x ^ j - y ^ j ≠ 0) :
    ordProj[2] (x - y).natAbs ≤ ordProj[2] (x ^ j - y ^ j).natAbs := by
  refine Nat.le_of_dvd (Nat.ordProj_pos _ _) (Nat.ordProj_dvd_ordProj_of_dvd ?_ ?_ 2)
  · exact Int.natAbs_ne_zero.mpr h
  · exact Int.natAbs_dvd_natAbs.mpr (sub_dvd_pow_sub_pow x y j)

theorem prod_le_prod_of_subset_of_pos {ι : Type*} {s t : Finset ι} (g : ι → ℕ) (hst : s ⊆ t)
    (hg : ∀ i ∈ t, 0 < g i) : ∏ i ∈ s, g i ≤ ∏ i ∈ t, g i := by
  classical
  rw [← prod_sdiff hst]
  exact Nat.le_mul_of_pos_left _ (prod_pos fun i hi => hg i (mem_sdiff.mp hi).1)

theorem ordProj_two_prod_sub_pow_ge {p f n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hn : 3 ≤ n) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ordProj[2] (Int.gcd (n : ℤ) ((p ^ f : ℕ) - ε)) ^ 2 * ordProj[2] ((p ^ f) ^ 2 - 1) ≤
      ∏ j ∈ Icc 2 n, ordProj[2] (((p ^ f : ℕ) : ℤ) ^ j - ε ^ j).natAbs := by
  set q := p ^ f with hq
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hq3 : 3 ≤ q := le_trans hp3 (by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf)
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hne : ∀ j : ℕ, 1 ≤ j → ((q : ℤ) ^ j - ε ^ j) ≠ 0 := by
    intro j hj
    have hqj : (3 : ℤ) ≤ (q : ℤ) ^ j := by
      calc (3 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq3
        _ = (q : ℤ) ^ 1 := (pow_one _).symm
        _ ≤ (q : ℤ) ^ j := pow_le_pow_right₀ (by omega) hj
    have hεj : ε ^ j ≤ 1 := by
      rcases hε with rfl | rfl
      · simp
      · rcases neg_one_pow_eq_or ℤ j with h | h <;> simp [h]
    omega
  set t : ℕ → ℕ := fun j => ordProj[2] (((q : ℕ) : ℤ) ^ j - ε ^ j).natAbs with ht
  have htpos : ∀ j ∈ Icc 2 n, 0 < t j := fun j _ => Nat.ordProj_pos _ _
  have ht2 : t 2 = ordProj[2] (q ^ 2 - 1) := by
    have h : ((q : ℤ) ^ 2 - ε ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
      rw [hε2, Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow q 2, Nat.cast_one]
    simp only [ht, h, Int.natAbs_natCast]
  set A := ordProj[2] ((q : ℤ) - ε).natAbs with hA
  have htA : ∀ j : ℕ, 1 ≤ j → A ≤ t j := fun j hj => ordProj_two_sub_le_sub_pow (hne j hj)
  set d := Int.gcd (n : ℤ) ((q : ℤ) - ε) with hd
  have hdA : ordProj[2] d ≤ A := by
    refine Nat.le_of_dvd (Nat.ordProj_pos _ _) (Nat.ordProj_dvd_ordProj_of_dvd ?_ ?_ 2)
    · exact Int.natAbs_ne_zero.mpr (by simpa using hne 1 le_rfl)
    · exact Int.ofNat_dvd_left.mp (Int.gcd_dvd_right _ _)
  rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | h4
  ·
    have hd1 : ordProj[2] d = 1 := by
      have hd3 : d ∣ 3 := Int.natCast_dvd_natCast.mp (Int.gcd_dvd_left _ _)
      have h2d : ¬2 ∣ d := fun h => absurd (h.trans hd3) (by norm_num)
      rw [Nat.factorization_eq_zero_of_not_dvd h2d, pow_zero]
    rw [hd1, one_pow, one_mul, ← ht2]
    calc t 2 = ∏ j ∈ {2}, t j := (prod_singleton _ _).symm
      _ ≤ ∏ j ∈ Icc 2 3, t j :=
        prod_le_prod_of_subset_of_pos t (by decide) htpos
  · calc ordProj[2] d ^ 2 * ordProj[2] (q ^ 2 - 1) ≤ A * A * t 2 := by
          rw [sq, ht2]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hdA hdA)
      _ ≤ t 3 * t 4 * t 2 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (htA 3 (by norm_num)) (htA 4 (by norm_num)))
      _ = ∏ j ∈ {2, 3, 4}, t j := by
          rw [prod_insert (by decide), prod_insert (by decide), prod_singleton]
          ring
      _ ≤ ∏ j ∈ Icc 2 n, t j := by
          refine prod_le_prod_of_subset_of_pos t ?_ htpos
          intro j hj
          simp only [mem_insert, mem_singleton] at hj
          rw [mem_Icc]
          omega

theorem ordProj_two_lt_two_pow {f : ℕ} (hf : 1 ≤ f) :
    ordProj[2] f < 2 ^ f ∧ 2 * ordProj[2] f < 2 ^ (3 * f) := by
  have h1 : ordProj[2] f ≤ f := Nat.ordProj_le 2 (by omega)
  have h2 : f < 2 ^ f := Nat.lt_two_pow_self
  refine ⟨h1.trans_lt h2, ?_⟩
  calc 2 * ordProj[2] f ≤ 2 * f := Nat.mul_le_mul_left 2 h1
    _ < 2 * 2 ^ f := Nat.mul_lt_mul_of_pos_left h2 (by norm_num)
    _ = 2 ^ (f + 1) := by rw [pow_succ, mul_comm]
    _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem lie_order_two_adic_arithmetic :
    (∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
      ordProj[2] ((p ^ f) ^ 2 - 1) = ordProj[2] (p ^ 2 - 1) * ordProj[2] f ∧
        8 * ordProj[2] f ≤ ordProj[2] ((p ^ f) ^ 2 - 1)) ∧
    (∀ p f n : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → 3 ≤ n → ∀ ε : ℤ, ε = 1 ∨ ε = -1 →
      ordProj[2] (Int.gcd (n : ℤ) ((p ^ f : ℕ) - ε)) ^ 2 * ordProj[2] ((p ^ f) ^ 2 - 1) ≤
        ∏ j ∈ Icc 2 n, ordProj[2] (((p ^ f : ℕ) : ℤ) ^ j - ε ^ j).natAbs) ∧
    (∀ f : ℕ, 1 ≤ f → ordProj[2] f < 2 ^ f ∧ 2 * ordProj[2] f < 2 ^ (3 * f)) :=
  ⟨fun _ _ hp hp2 hf =>
      ⟨ordProj_two_pow_sq_sub_one hp hp2 hf, eight_mul_ordProj_two_le hp hp2 hf⟩,
    fun _ _ _ hp hp2 hf hn _ hε => ordProj_two_prod_sub_pow_ge hp hp2 hf hn hε,
    fun _ hf => ordProj_two_lt_two_pow hf⟩

end CFSG.LocalAnalysis.ComponentInitial
