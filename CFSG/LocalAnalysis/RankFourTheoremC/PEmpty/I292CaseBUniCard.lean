module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LinearGroups

variable {r f : ℕ} {K : Type} [Field K]

theorem toLin_mem_sesqUnitaryGroup_iff {n : ℕ} (h : UnitaryFieldData r f K)
    (G : Matrix (Fin n) (Fin n) K) (g : GL (Fin n) K) :
    Matrix.GeneralLinearGroup.toLin g ∈ sesqUnitaryGroup (gramForm h G) ↔
      g ∈ primeFormUnitary h G := by
  rw [mem_sesqUnitaryGroup, mem_primeFormUnitary, ← gramForm_isometry_iff]
  simp only [Matrix.GeneralLinearGroup.coe_toLin, Matrix.toLin'_apply, Matrix.mulVecLin_apply]

theorem card_primeFormUnitary_eq {n : ℕ} (h : UnitaryFieldData r f K)
    (G : Matrix (Fin n) (Fin n) K) :
    Nat.card (primeFormUnitary h G) = Nat.card (sesqUnitaryGroup (gramForm h G)) :=
  Nat.card_congr (Matrix.GeneralLinearGroup.toLin.toEquiv.subtypeEquiv fun g =>
    (toLin_mem_sesqUnitaryGroup_iff h G g).symm)

theorem card_primeFormUnitary_int (h : UnitaryFieldData r f K) {n : ℕ} (hn : 1 ≤ n) :
    (Nat.card (primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : ℤ) =
      ((r ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
        ∏ i ∈ Finset.Icc 1 n, (((r ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  have hU := (unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin n) (Fin n) K)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun _) hn).1
  rw [card_primeFormUnitary_eq h]
  exact hU

@[expose] def uFactor (q i : ℕ) : ℕ := if Even i then q ^ i - 1 else q ^ i + 1

theorem cast_uFactor {q : ℕ} (hq : 1 ≤ q) (i : ℕ) :
    ((uFactor q i : ℕ) : ℤ) = (q : ℤ) ^ i - (-1) ^ i := by
  unfold uFactor
  by_cases hi : Even i
  · rw [if_pos hi, hi.neg_one_pow, Nat.cast_sub (Nat.one_le_pow _ _ hq)]
    push_cast
    ring
  · rw [if_neg hi, (Nat.not_even_iff_odd.1 hi).neg_one_pow]
    push_cast
    ring

theorem factorization_uFactor {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 2 ≤ q)
    (hpq : p ∣ q + 1) {i : ℕ} (hi : i ≠ 0) :
    (uFactor q i).factorization p = (q + 1).factorization p + i.factorization p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpq0 : ¬ p ∣ q := by
    intro h1
    have h2 : p ∣ (q + 1) - q := Nat.dvd_sub hpq h1
    rw [show (q + 1) - q = 1 by omega] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, Nat.factorization_def _ hp]
  unfold uFactor
  by_cases hev : Even i
  · rw [if_pos hev]
    obtain ⟨m, hm⟩ := hev
    have hm0 : m ≠ 0 := by omega
    have h2m : i = 2 * m := by omega
    have hq2 : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    have hpq1 : ¬ p ∣ q - 1 := by
      intro h1
      have h2 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub hpq h1
      rw [show (q + 1) - (q - 1) = 2 by omega] at h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
    have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      zify [Nat.one_le_pow 2 q (by omega), (by omega : 1 ≤ q)]
      ring
    have hdvd : p ∣ q ^ 2 - 1 := by
      rw [hfac]
      exact Dvd.dvd.mul_left hpq _
    have hnq2 : ¬ p ∣ q ^ 2 := fun h1 => hpq0 (hp.dvd_of_dvd_pow h1)
    have hlte := padicValNat.pow_sub_pow (p := p) hodd (x := q ^ 2) (y := 1) hq2 hdvd hnq2 hm0
    rw [one_pow, ← pow_mul, ← h2m] at hlte
    rw [hlte, hfac, padicValNat.mul (by omega) (by omega),
      padicValNat.eq_zero_of_not_dvd hpq1, zero_add, h2m,
      padicValNat.mul (by norm_num) hm0, padicValNat.eq_zero_of_not_dvd
        (fun h1 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h1)), zero_add]
  · rw [if_neg hev]
    have hio : Odd i := Nat.not_even_iff_odd.1 hev
    have hlte := padicValNat.pow_add_pow (p := p) hodd (x := q) (y := 1) hpq hpq0 hio
    rwa [one_pow] at hlte

theorem sum_factorization_Icc {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ∑ i ∈ Finset.Icc 1 p, (a + i.factorization p) = p * a + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have h1 : ∑ i ∈ Finset.Icc 1 m, i.factorization (m + 1) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    exact Nat.factorization_eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel,
    Finset.sum_Icc_succ_top (by omega), h1, zero_add, Nat.Prime.factorization_self hp]

theorem factorization_card_primeFormUnitary {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : UnitaryFieldData r f K) (hpq : p ∣ r ^ f + 1) :
    (Nat.card (primeFormUnitary h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K))).factorization
        p = p * (r ^ f + 1).factorization p + 1 := by
  have hq : 2 ≤ r ^ f := h.one_lt_pow
  have hint := card_primeFormUnitary_int h hp.pos
  have hpq0 : ¬ p ∣ r ^ f := by
    intro h1
    have h2 : p ∣ (r ^ f + 1) - r ^ f := Nat.dvd_sub hpq h1
    rw [show (r ^ f + 1) - r ^ f = 1 by omega] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have hnat : Nat.card (primeFormUnitary h ((1 : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)) =
      (r ^ f) ^ (p * (p - 1) / 2) * ∏ i ∈ Finset.Icc 1 p, uFactor (r ^ f) i := by
    have h1 : ((Nat.card (primeFormUnitary h ((1 : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K)) : ℕ) : ℤ) =
        (((r ^ f) ^ (p * (p - 1) / 2) * ∏ i ∈ Finset.Icc 1 p, uFactor (r ^ f) i : ℕ) : ℤ) := by
      rw [hint]
      push_cast
      congr 1
      exact Finset.prod_congr rfl fun i _ => (cast_uFactor (by omega) i).symm
    exact_mod_cast h1
  have hne : ∀ i ∈ Finset.Icc 1 p, uFactor (r ^ f) i ≠ 0 := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
    have hcast := cast_uFactor (by omega : 1 ≤ r ^ f) i
    intro h0
    rw [h0] at hcast
    have hlt : ((r ^ f : ℕ) : ℤ) ^ i - (-1) ^ i = 0 := by simpa using hcast.symm
    rcases Nat.even_or_odd i with hev | hodd
    · rw [hev.neg_one_pow] at hlt
      have : (1 : ℤ) < ((r ^ f : ℕ) : ℤ) ^ i := by
        have := Nat.one_lt_pow (n := i) (by omega) (by omega : 1 < r ^ f)
        exact_mod_cast this
      linarith
    · rw [hodd.neg_one_pow] at hlt
      have : (0 : ℤ) < ((r ^ f : ℕ) : ℤ) ^ i := by positivity
      linarith
  have hpow0 : (r ^ f) ^ (p * (p - 1) / 2) ≠ 0 := pow_ne_zero _ (by omega)
  rw [hnat, Nat.factorization_mul hpow0 (Finset.prod_ne_zero_iff.2 hne), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.factorization_prod hne, Finsupp.coe_finset_sum,
    Finset.sum_apply]
  have hz : (r ^ f).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpq0
  rw [hz, smul_zero, zero_add]
  rw [Finset.sum_congr rfl (fun i hi => factorization_uFactor hp hp2 hq hpq
    (by have := (Finset.mem_Icc.1 hi).1; omega))]
  exact sum_factorization_Icc hp _

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseB
