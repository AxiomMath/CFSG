module

public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.HardMathSupport.Timmesfeld.LinearRank

theorem not_dvd_of_dvd_sub_one {p q : ℕ} (hp : p.Prime) (hq : 1 < q) (hpq : p ∣ q - 1) :
    ¬ p ∣ q := fun h => hp.one_lt.ne' <| Nat.dvd_one.mp <| by
  simpa [Nat.sub_sub_self hq.le] using Nat.dvd_sub h hpq

theorem factorization_pow_sub_one {p q j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 < q)
    (hpq : p ∣ q - 1) (hj : j ≠ 0) :
    (q ^ j - 1).factorization p = (q - 1).factorization p + j.factorization p := by
  have := Fact.mk hp
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  simpa using padicValNat.pow_sub_pow (hp.odd_of_ne_two hp2) hq hpq
    (not_dvd_of_dvd_sub_one hp hq hpq) hj

theorem sum_factorization_sub_eq (p n : ℕ) :
    ∑ i : Fin n, (n - i).factorization p = n.factorial.factorization p := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (n - i).factorization p), ← Finset.sum_range_reflect,
    ← Finset.prod_range_add_one_eq_factorial,
    Nat.factorization_prod fun i _ => Nat.add_one_ne_zero i, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [show n - (n - 1 - i) = i + 1 by omega]

theorem factorization_prod_pow_sub_pow {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 < q)
    (hpq : p ∣ q - 1) (n : ℕ) :
    (∏ i : Fin n, (q ^ n - q ^ (i : ℕ))).factorization p =
      ((q - 1) ^ n * n.factorial).factorization p := by
  have hq0 : q ≠ 0 := by omega
  have hsplit : ∀ i : Fin n, q ^ n - q ^ (i : ℕ) = q ^ (i : ℕ) * (q ^ (n - i) - 1) := fun i => by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_of_le i.isLt.le]
  have hne : ∀ i : Fin n, q ^ (n - i) - 1 ≠ 0 := fun i => by
    have := Nat.one_lt_pow (Nat.sub_ne_zero_of_lt i.isLt) hq
    omega
  have hterm : ∀ i : Fin n, (q ^ n - q ^ (i : ℕ)).factorization p =
      (q - 1).factorization p + (n - i).factorization p := fun i => by
    rw [hsplit i, Nat.factorization_mul (pow_ne_zero _ hq0) (hne i), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_zero_of_not_dvd (not_dvd_of_dvd_sub_one hp hq hpq), mul_zero,
      zero_add, factorization_pow_sub_one hp hp2 hq hpq (Nat.sub_ne_zero_of_lt i.isLt)]
  have hprod : ∀ i ∈ (Finset.univ : Finset (Fin n)), q ^ n - q ^ (i : ℕ) ≠ 0 := fun i _ => by
    rw [hsplit i]
    exact mul_ne_zero (pow_ne_zero _ hq0) (hne i)
  rw [Nat.factorization_prod hprod, Finsupp.finsetSum_apply]
  simp only [hterm]
  rw [Finset.sum_add_distrib, sum_factorization_sub_eq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul,
    Nat.factorization_mul (pow_ne_zero _ (by omega)) n.factorial_ne_zero, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

theorem factorization_card_GL_eq {K : Type} [Field K] [Finite K] {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : p ∣ Nat.card Kˣ) :
    (Nat.card (Matrix.GeneralLinearGroup (Fin n) K)).factorization p =
      ((Nat.card Kˣ) ^ n * n.factorial).factorization p := by
  have := Fintype.ofFinite K
  rw [Nat.card_units, Nat.card_eq_fintype_card (α := K)] at hpK ⊢
  rw [Matrix.card_GL_field]
  exact factorization_prod_pow_sub_pow hp hp2 Fintype.one_lt_card hpK n

theorem not_dvd_index_of_card_eq {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (M : Subgroup G) (h : (Nat.card G).factorization p = (Nat.card M).factorization p) :
    ¬ p ∣ M.index := by
  intro hdvd
  have hidx : M.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [← M.card_mul_index, Nat.factorization_mul Nat.card_pos.ne' hidx, Finsupp.add_apply] at h
  have := (hp.dvd_iff_one_le_factorization hidx).mp hdvd
  omega

end CFSG.HardMathSupport.Timmesfeld.LinearRank
