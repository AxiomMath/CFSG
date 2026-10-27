module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

@[expose] def lieOrderCofactor : StatedLieTag → ℕ → ℕ → ℕ
  | .PSL, n, q => ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1)
  | .PSU, n, q => ∏ i ∈ Finset.Icc 2 n, (if Even i then q ^ i - 1 else q ^ i + 1)
  | .PSp, n, q => ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1)
  | .POmegaOdd, n, q => ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1)
  | .POmegaPlus, n, q => (q ^ n - 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)
  | .POmegaMinus, n, q => (q ^ n + 1) * ∏ i ∈ Finset.Icc 1 (n - 1), (q ^ (2 * i) - 1)
  | .G2, _, q => (q ^ 6 - 1) * (q ^ 2 - 1)
  | .F4, _, q => (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
  | .E6, _, q => (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
      (q ^ 2 - 1)
  | .E7, _, q => (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
      (q ^ 6 - 1) * (q ^ 2 - 1)
  | .E8, _, q => (q ^ 30 - 1) * (q ^ 24 - 1) * (q ^ 20 - 1) * (q ^ 18 - 1) * (q ^ 14 - 1) *
      (q ^ 12 - 1) * (q ^ 8 - 1) * (q ^ 2 - 1)
  | .twistedE6, _, q => (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) *
      (q ^ 2 - 1)
  | .trialityD4, _, q => (q ^ 8 + q ^ 4 + 1) * (q ^ 6 - 1) * (q ^ 2 - 1)
  | .twistedB2, _, q => (q ^ 2 + 1) * (q - 1)
  | .twistedG2, _, q => (q ^ 3 + 1) * (q - 1)
  | .twistedF4, _, q => (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1)
  | .Tits, _, _ => 8775

theorem lieOrderNumerator_eq {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f) :
    lieOrderNumerator t n (p ^ f) =
      (p ^ f) ^ lieSylowExponent t n * lieOrderCofactor t n (p ^ f) := by
  cases t
  case Tits =>
    obtain ⟨-, -, -, rfl, rfl⟩ := hadm
    norm_num [lieOrderNumerator, lieOrderCofactor, lieSylowExponent]
  all_goals simp only [lieOrderNumerator, lieOrderCofactor, lieSylowExponent, mul_assoc]

theorem coprime_pow_sub_one {p q i : ℕ} (hp : p.Prime) (hpq : p ∣ q) (hq : 1 ≤ q)
    (hi : 1 ≤ i) : Nat.Coprime (q ^ i - 1) p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro h
  have h1 : p ∣ q ^ i := dvd_pow hpq (by omega)
  have h2 : p ∣ q ^ i - (q ^ i - 1) := Nat.dvd_sub h1 h
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hq)] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

theorem coprime_pow_add_one {p q i : ℕ} (hp : p.Prime) (hpq : p ∣ q) (hi : 1 ≤ i) :
    Nat.Coprime (q ^ i + 1) p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro h
  have h1 : p ∣ q ^ i := dvd_pow hpq (by omega)
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp h))

theorem coprime_triality_factor {p q : ℕ} (hp : p.Prime) (hpq : p ∣ q) :
    Nat.Coprime (q ^ 8 + q ^ 4 + 1) p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro h
  have h1 : p ∣ q ^ 8 + q ^ 4 := dvd_add (dvd_pow hpq (by norm_num)) (dvd_pow hpq (by norm_num))
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp h))

theorem lieOrderCofactor_coprime {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) : Nat.Coprime (lieOrderCofactor t n (p ^ f)) p := by
  have hp := hadm.1
  have hf := hadm.2.1
  have hpq : p ∣ p ^ f := dvd_pow_self p (by omega)
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hs : ∀ i, 1 ≤ i → Nat.Coprime ((p ^ f) ^ i - 1) p := fun i hi =>
    coprime_pow_sub_one hp hpq hq hi
  have ha : ∀ i, 1 ≤ i → Nat.Coprime ((p ^ f) ^ i + 1) p := fun i hi =>
    coprime_pow_add_one hp hpq hi
  have h1 : Nat.Coprime (p ^ f - 1) p := by simpa using hs 1 le_rfl
  cases t
  case PSL => exact Nat.Coprime.prod_left fun i hi => hs i (by simp at hi; omega)
  case PSU =>
    refine Nat.Coprime.prod_left fun i hi => ?_
    have hi' : 1 ≤ i := by simp at hi; omega
    split_ifs
    · exact hs i hi'
    · exact ha i hi'
  case PSp => exact Nat.Coprime.prod_left fun i hi => hs _ (by simp at hi; omega)
  case POmegaOdd => exact Nat.Coprime.prod_left fun i hi => hs _ (by simp at hi; omega)
  case POmegaPlus =>
    obtain ⟨-, -, hn⟩ := hadm
    exact Nat.Coprime.mul_left (hs n (by omega))
      (Nat.Coprime.prod_left fun i hi => hs _ (by simp at hi; omega))
  case POmegaMinus =>
    obtain ⟨-, -, hn⟩ := hadm
    exact Nat.Coprime.mul_left (ha n (by omega))
      (Nat.Coprime.prod_left fun i hi => hs _ (by simp at hi; omega))
  case Tits =>
    obtain ⟨-, -, -, rfl, -⟩ := hadm
    show Nat.Coprime 8775 2
    decide
  case trialityD4 =>
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_left (coprime_triality_factor hp hpq)
      (hs 6 (by norm_num))) (hs 2 (by norm_num))
  case twistedB2 => exact Nat.Coprime.mul_left (ha 2 (by norm_num)) h1
  case twistedG2 => exact Nat.Coprime.mul_left (ha 3 (by norm_num)) h1
  case twistedF4 =>
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_left (Nat.Coprime.mul_left (ha 6 (by norm_num))
      (hs 4 (by norm_num))) (ha 3 (by norm_num))) h1
  all_goals
    simp only [lieOrderCofactor]
    repeat' first
      | exact hs _ (by norm_num)
      | exact ha _ (by norm_num)
      | refine Nat.Coprime.mul_left ?_ ?_

theorem lieOrderCofactor_ne_zero {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) : lieOrderCofactor t n (p ^ f) ≠ 0 := by
  have hc := lieOrderCofactor_coprime hadm
  intro h0
  rw [h0, Nat.coprime_zero_left] at hc
  exact hadm.1.one_lt.ne' hc

theorem sub_one_dvd_sq_sub_one (q : ℕ) : q - 1 ∣ q ^ 2 - 1 := by
  simpa using Nat.sub_dvd_pow_sub_pow q 1 2

theorem add_one_dvd_sq_sub_one (q : ℕ) : q + 1 ∣ q ^ 2 - 1 := by
  rw [show q ^ 2 - 1 = q ^ 2 - 1 ^ 2 by norm_num, Nat.sq_sub_sq]
  exact dvd_mul_right _ _

theorem lieOrderDivisor_dvd_cofactor {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) :
    lieOrderDivisor t n (p ^ f) ∣ lieOrderCofactor t n (p ^ f) := by
  set q := p ^ f with hq
  cases t
  case PSL =>
    obtain ⟨-, -, hn, -, -⟩ := hadm
    have h2 : (2 : ℕ) ∈ Finset.Icc 2 n := by simp; omega
    exact (Nat.gcd_dvd_right _ _).trans ((sub_one_dvd_sq_sub_one q).trans
      (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) h2))
  case PSU =>
    obtain ⟨-, -, hn, -⟩ := hadm
    have h2 : (2 : ℕ) ∈ Finset.Icc 2 n := by simp; omega
    have h := Finset.dvd_prod_of_mem (fun i => if Even i then q ^ i - 1 else q ^ i + 1) h2
    simp only [even_two, ite_true] at h
    exact (Nat.gcd_dvd_right _ _).trans ((add_one_dvd_sq_sub_one q).trans h)
  case PSp =>
    obtain ⟨-, -, hn, -⟩ := hadm
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 n := by simp; omega
    have h := Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) h1
    simp only [mul_one] at h
    exact (Nat.gcd_dvd_right _ _).trans ((sub_one_dvd_sq_sub_one q).trans h)
  case POmegaOdd =>
    obtain ⟨hp, -, hn, hp2⟩ := hadm
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 n := by simp; omega
    have h := Finset.dvd_prod_of_mem (fun i => q ^ (2 * i) - 1) h1
    simp only [mul_one] at h
    have hodd : Odd q := (hp.eq_two_or_odd'.resolve_left hp2).pow
    have he : Even (q ^ 2 - 1) := Nat.Odd.sub_odd hodd.pow odd_one
    exact (even_iff_two_dvd.mp he).trans h
  case POmegaPlus => exact (Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _)
  case POmegaMinus => exact (Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _)
  case E6 => exact (Nat.gcd_dvd_right _ _).trans ((sub_one_dvd_sq_sub_one q).trans
      (dvd_mul_left _ _))
  case E7 => exact (Nat.gcd_dvd_right _ _).trans ((sub_one_dvd_sq_sub_one q).trans
      (dvd_mul_left _ _))
  case twistedE6 => exact (Nat.gcd_dvd_right _ _).trans ((add_one_dvd_sq_sub_one q).trans
      (dvd_mul_left _ _))
  all_goals exact one_dvd _

theorem not_dvd_lieOrderDivisor {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) : ¬ p ∣ lieOrderDivisor t n (p ^ f) := fun h =>
  (Nat.Prime.coprime_iff_not_dvd hadm.1).mp ((lieOrderCofactor_coprime hadm).symm)
    (h.trans (lieOrderDivisor_dvd_cofactor hadm))

theorem lieOrderDivisor_ne_zero {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) : lieOrderDivisor t n (p ^ f) ≠ 0 := fun h0 =>
  lieOrderCofactor_ne_zero hadm (Nat.eq_zero_of_zero_dvd (h0 ▸ lieOrderDivisor_dvd_cofactor hadm))

theorem lieOrderDivisor_dvd_numerator {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) :
    lieOrderDivisor t n (p ^ f) ∣ lieOrderNumerator t n (p ^ f) := by
  rw [lieOrderNumerator_eq hadm]
  exact (lieOrderDivisor_dvd_cofactor hadm).mul_left _

theorem factorization_lieOrderNumerator {t : StatedLieTag} {n p f : ℕ}
    (hadm : StatedLieAdmissible t n p f) :
    (lieOrderNumerator t n (p ^ f)).factorization p = lieSylowExponent t n * f := by
  have hp := hadm.1
  rw [lieOrderNumerator_eq hadm, ← pow_mul,
    Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (lieOrderCofactor_ne_zero hadm),
    Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd
      ((Nat.Prime.coprime_iff_not_dvd hp).mp (lieOrderCofactor_coprime hadm).symm), add_zero,
    mul_comm]

end CFSG.ComponentClassification.CatLeafProof
