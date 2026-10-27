module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Finset

section Valuation

variable {p q : ℕ} [hp : Fact p.Prime]

theorem padicValNat_pow_sub_one_eq (hp2 : Odd p) (hq : ¬ p ∣ q) (hq1 : 1 < q) {e : ℕ}
    (he : 0 < e) (hpe : ∀ j : ℕ, p ∣ q ^ j - 1 ↔ e ∣ j) {j : ℕ} (hj0 : 0 < j) (hj : j / e < p) :
    padicValNat p (q ^ j - 1) = if e ∣ j then padicValNat p (q ^ e - 1) else 0 := by
  split_ifs with hej
  · obtain ⟨t, rfl⟩ := hej
    have ht : 0 < t := Nat.pos_of_mul_pos_left hj0
    have hte : e * t / e = t := Nat.mul_div_cancel_left t he
    rw [hte] at hj
    have hqe : 1 < q ^ e := Nat.one_lt_pow he.ne' hq1
    have hdiv : p ∣ q ^ e - 1 ^ 1 := by simpa using (hpe e).2 dvd_rfl
    have hnd : ¬ p ∣ q ^ e := fun h => hq (hp.out.dvd_of_dvd_pow h)
    have := padicValNat.pow_sub_pow (p := p) hp2 (x := q ^ e) (y := 1) hqe hdiv hnd ht.ne'
    rw [one_pow, ← pow_mul] at this
    rw [this, padicValNat.eq_zero_of_not_dvd (n := t), add_zero]
    exact fun h => absurd (Nat.le_of_dvd ht h) (not_le.2 hj)
  · exact padicValNat.eq_zero_of_not_dvd (fun h => hej ((hpe j).1 h))

theorem padicValNat_prod_range {f : ℕ → ℕ} (hf : ∀ i, f i ≠ 0) (n : ℕ) :
    padicValNat p (∏ i ∈ range n, f i) = ∑ i ∈ range n, padicValNat p (f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, sum_range_succ,
      padicValNat.mul (Finset.prod_ne_zero_iff.2 fun i _ => hf i) (hf n), ih]

theorem sum_range_sub_eq_sum_Ioc (g : ℕ → ℕ) (n : ℕ) :
    ∑ i ∈ range n, g (n - i) = ∑ j ∈ Ioc 0 n, g j := by
  have h1 : ∑ i ∈ range n, g (n - i) = ∑ i ∈ range n, g (n - 1 - i + 1) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    congr 1
    omega
  rw [h1, Finset.sum_range_reflect (fun i => g (i + 1)) n]
  clear h1
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, Finset.sum_Ioc_succ_top (Nat.zero_le n)]

end Valuation

section Cardinality

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [Field K] [Finite K]

theorem padicValNat_card_GL {n e : ℕ} (hp2 : Odd p) (hpK : ¬ p ∣ Nat.card K) (he : 0 < e)
    (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j) (hne : n / e < p) :
    padicValNat p (Nat.card (GL (Fin n) K)) = (n / e) * padicValNat p (Nat.card K ^ e - 1) := by
  haveI := Fintype.ofFinite K
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hcard : Fintype.card K = Nat.card K := (Nat.card_eq_fintype_card).symm
  set q := Nat.card K with hq
  rw [Matrix.card_GL_field, hcard, Fin.prod_univ_eq_prod_range (fun i => q ^ n - q ^ i) n]
  have hterm : ∀ i ∈ range n,
      padicValNat p (q ^ n - q ^ i) = padicValNat p (q ^ (n - i) - 1) := by
    intro i hi
    have hin : i ≤ n := (Finset.mem_range.1 hi).le
    have hlt : 0 < q ^ (n - i) - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow
      (by have := Finset.mem_range.1 hi; omega) hq1)
    have hsplit : q ^ n - q ^ i = q ^ i * (q ^ (n - i) - 1) := by
      rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hin]
    have h0 : padicValNat p (q ^ i) = 0 :=
      padicValNat.eq_zero_of_not_dvd (fun h => hpK (hp.out.dvd_of_dvd_pow h))
    rw [hsplit, padicValNat.mul (pow_ne_zero _ (by omega)) hlt.ne', h0, zero_add]
  have hne0 : ∀ i, (if i < n then q ^ n - q ^ i else 1) ≠ 0 := by
    intro i
    split_ifs with hi
    · exact Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_right hq1 hi)
    · exact one_ne_zero
  have hprod : ∏ i ∈ range n, (q ^ n - q ^ i) =
      ∏ i ∈ range n, (if i < n then q ^ n - q ^ i else 1) :=
    Finset.prod_congr rfl fun i hi => by rw [if_pos (Finset.mem_range.1 hi)]
  rw [hprod, padicValNat_prod_range hne0]
  have hsum : ∑ i ∈ range n, padicValNat p (if i < n then q ^ n - q ^ i else 1) =
      ∑ i ∈ range n, padicValNat p (q ^ (n - i) - 1) :=
    Finset.sum_congr rfl fun i hi => by
      rw [if_pos (Finset.mem_range.1 hi)]
      exact hterm i hi
  rw [hsum, sum_range_sub_eq_sum_Ioc (fun j => padicValNat p (q ^ j - 1)) n]
  have hval : ∀ j ∈ Ioc 0 n, padicValNat p (q ^ j - 1) =
      if e ∣ j then padicValNat p (q ^ e - 1) else 0 := by
    intro j hj
    rw [Finset.mem_Ioc] at hj
    exact padicValNat_pow_sub_one_eq hp2 hpK hq1 he hpe hj.1
      (lt_of_le_of_lt (Nat.div_le_div_right hj.2) hne)
  rw [Finset.sum_congr rfl hval, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    smul_eq_mul, Nat.Ioc_filter_dvd_card_eq_div, mul_comm]

end Cardinality

end CFSG.LocalAnalysis.RankFourTheoremC
