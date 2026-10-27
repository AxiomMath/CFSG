module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36LieInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

namespace OddChar

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

variable {Q : ℕ}

theorem pow_add_one_le_pow_succ (hQ : 2 ≤ Q) (i : ℕ) : Q ^ i + 1 ≤ Q ^ (i + 1) := by
  rw [pow_succ]
  have : 1 ≤ Q ^ i := Nat.one_le_pow _ _ (by omega)
  nlinarith

theorem mul_le_pow_add {a b i j : ℕ} (ha : a ≤ Q ^ i) (hb : b ≤ Q ^ j) : a * b ≤ Q ^ (i + j) := by
  rw [pow_add]
  exact Nat.mul_le_mul ha hb

theorem pow_sub_one_le (i : ℕ) : Q ^ i - 1 ≤ Q ^ i := Nat.sub_le _ _

theorem mul_sq_sub_one_lt (hQ : 1 ≤ Q) : Q * (Q ^ 2 - 1) < Q ^ 3 := by
  have h1 : Q ^ 2 - 1 < Q ^ 2 := Nat.sub_lt (Nat.one_le_pow _ _ hQ) one_pos
  calc Q * (Q ^ 2 - 1) < Q * Q ^ 2 := Nat.mul_lt_mul_of_pos_left h1 hQ
    _ = Q ^ 3 := by ring

theorem lt_pow_of_le_pow {a b c : ℕ} (hQ : 1 < Q) (h : c ≤ Q ^ a) (hab : a < b) : c < Q ^ b :=
  h.trans_lt (Nat.pow_lt_pow_right hQ hab)

theorem lt_pow_two_mul_of_lt {a M : ℕ} (h : Q ^ a * M < Q ^ (3 * a)) : M < Q ^ (2 * a) := by
  have h1 : Q ^ (3 * a) = Q ^ a * Q ^ (2 * a) := by rw [← pow_add]; ring_nf
  rw [h1] at h
  exact Nat.lt_of_mul_lt_mul_left h

theorem psl_lt (hQ : 2 ≤ Q) {n : ℕ} (hn : 2 ≤ n) :
    Q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (Q ^ i - 1) < Q ^ (3 * (n * (n - 1) / 2)) := by
  have hQ0 : 0 < Q := by omega
  induction n, hn using Nat.le_induction with
  | base =>
    norm_num
    exact mul_sq_sub_one_lt (by omega)
  | succ n hn ih =>
    rw [Finset.prod_Icc_succ_top (by omega), Nat.triangle_succ]
    calc Q ^ (n * (n - 1) / 2 + n) * ((∏ i ∈ Finset.Icc 2 n, (Q ^ i - 1)) * (Q ^ (n + 1) - 1))
        = (Q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (Q ^ i - 1)) *
            (Q ^ n * (Q ^ (n + 1) - 1)) := by rw [pow_add]; ring
      _ < Q ^ (3 * (n * (n - 1) / 2)) * (Q ^ n * Q ^ (n + 1)) :=
          Nat.mul_lt_mul_of_lt_of_le ih (Nat.mul_le_mul_left _ (pow_sub_one_le _))
            (by positivity)
      _ = Q ^ (3 * (n * (n - 1) / 2) + (2 * n + 1)) := by rw [← pow_add, ← pow_add]; ring_nf
      _ ≤ Q ^ (3 * (n * (n - 1) / 2 + n)) := Nat.pow_le_pow_right hQ0 (by omega)

theorem psu_lt (hQ : 2 ≤ Q) {n : ℕ} (hn : 3 ≤ n) :
    Q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (if Even i then Q ^ i - 1 else Q ^ i + 1) <
      Q ^ (3 * (n * (n - 1) / 2)) := by
  have hQ0 : 0 < Q := by omega
  have hg : ∀ i, (if Even i then Q ^ i - 1 else Q ^ i + 1) ≤ Q ^ (i + 1) := by
    intro i
    split_ifs
    · exact (pow_sub_one_le i).trans (Nat.pow_le_pow_right hQ0 (by omega))
    · exact pow_add_one_le_pow_succ hQ i
  induction n, hn using Nat.le_induction with
  | base =>
    rw [show (3 : ℕ) * (3 - 1) / 2 = 3 by norm_num, show (3 : ℕ) = 2 + 1 by rfl,
      Finset.prod_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.prod_singleton]
    have h2 : Even 2 := even_two
    have h3 : ¬ Even (2 + 1) := by decide
    rw [ite_eq_left h2, ite_eq_right h3]
    have ha : Q ^ 2 - 1 + 1 = Q ^ 2 := Nat.sub_add_cancel (Nat.one_le_pow _ _ hQ0)
    have hb : Q ^ 2 - 1 ≤ Q ^ (2 + 1) :=
      (pow_sub_one_le 2).trans (Nat.pow_le_pow_right hQ0 (by norm_num))
    have h5 : (Q ^ 2 - 1) * (Q ^ (2 + 1) + 1) ≤ Q ^ 5 := by
      calc (Q ^ 2 - 1) * (Q ^ (2 + 1) + 1) = (Q ^ 2 - 1) * Q ^ (2 + 1) + (Q ^ 2 - 1) := by ring
        _ ≤ (Q ^ 2 - 1) * Q ^ (2 + 1) + Q ^ (2 + 1) := Nat.add_le_add_left hb _
        _ = (Q ^ 2 - 1 + 1) * Q ^ (2 + 1) := by ring
        _ = Q ^ 5 := by rw [ha]; ring
    calc Q ^ (2 + 1) * ((Q ^ 2 - 1) * (Q ^ (2 + 1) + 1)) ≤ Q ^ (2 + 1) * Q ^ 5 :=
          Nat.mul_le_mul_left _ h5
      _ < Q ^ (3 * (2 + 1)) := by
          rw [← pow_add]
          exact Nat.pow_lt_pow_right (by omega) (by norm_num)
  | succ n hn ih =>
    rw [Finset.prod_Icc_succ_top (by omega), Nat.triangle_succ]
    calc Q ^ (n * (n - 1) / 2 + n) * ((∏ i ∈ Finset.Icc 2 n,
          (if Even i then Q ^ i - 1 else Q ^ i + 1)) *
          (if Even (n + 1) then Q ^ (n + 1) - 1 else Q ^ (n + 1) + 1))
        = (Q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n,
            (if Even i then Q ^ i - 1 else Q ^ i + 1)) *
            (Q ^ n * (if Even (n + 1) then Q ^ (n + 1) - 1 else Q ^ (n + 1) + 1)) := by
          rw [pow_add]; ring
      _ < Q ^ (3 * (n * (n - 1) / 2)) * (Q ^ n * Q ^ (n + 1 + 1)) :=
          Nat.mul_lt_mul_of_lt_of_le ih (Nat.mul_le_mul_left _ (hg (n + 1))) (by positivity)
      _ = Q ^ (3 * (n * (n - 1) / 2) + (2 * n + 2)) := by rw [← pow_add, ← pow_add]; ring_nf
      _ ≤ Q ^ (3 * (n * (n - 1) / 2 + n)) := Nat.pow_le_pow_right hQ0 (by omega)

theorem psp_lt (hQ : 2 ≤ Q) {n : ℕ} (hn : 1 ≤ n) :
    Q ^ (n ^ 2) * ∏ i ∈ Finset.Icc 1 n, (Q ^ (2 * i) - 1) < Q ^ (3 * n ^ 2) := by
  have hQ0 : 0 < Q := by omega
  induction n, hn using Nat.le_induction with
  | base =>
    norm_num
    exact mul_sq_sub_one_lt (by omega)
  | succ n hn ih =>
    rw [Finset.prod_Icc_succ_top (by omega)]
    rw [show 3 * (n + 1) ^ 2 = 3 * n ^ 2 + (6 * n + 3) by ring,
      show (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) by ring]
    calc Q ^ (n ^ 2 + (2 * n + 1)) * ((∏ i ∈ Finset.Icc 1 n, (Q ^ (2 * i) - 1)) *
          (Q ^ (2 * (n + 1)) - 1))
        = (Q ^ (n ^ 2) * ∏ i ∈ Finset.Icc 1 n, (Q ^ (2 * i) - 1)) *
            (Q ^ (2 * n + 1) * (Q ^ (2 * (n + 1)) - 1)) := by rw [pow_add]; ring
      _ < Q ^ (3 * n ^ 2) * (Q ^ (2 * n + 1) * Q ^ (2 * (n + 1))) :=
          Nat.mul_lt_mul_of_lt_of_le ih (Nat.mul_le_mul_left _ (pow_sub_one_le _))
            (by positivity)
      _ = Q ^ (3 * n ^ 2 + (4 * n + 3)) := by rw [← pow_add, ← pow_add]; ring_nf
      _ ≤ Q ^ (3 * n ^ 2 + (6 * n + 3)) := Nat.pow_le_pow_right hQ0 (by omega)

theorem omega_lt (hQ : 2 ≤ Q) {n c : ℕ} (hn : 4 ≤ n) (hc : c ≤ Q ^ (n + 1)) :
    Q ^ (n * (n - 1)) * c * ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1) <
      Q ^ (3 * (n * (n - 1))) := by
  have hQ0 : 0 < Q := by omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hP := lt_pow_two_mul_of_lt (psp_lt hQ (n := m) (by omega))
  calc Q ^ ((m + 1) * m) * c * ∏ i ∈ Finset.Icc 1 m, (Q ^ (2 * i) - 1)
      ≤ Q ^ ((m + 1) * m + (m + 1 + 1)) * ∏ i ∈ Finset.Icc 1 m, (Q ^ (2 * i) - 1) :=
        Nat.mul_le_mul_right _ (mul_le_pow_add le_rfl hc)
    _ < Q ^ ((m + 1) * m + (m + 1 + 1)) * Q ^ (2 * m ^ 2) :=
        Nat.mul_lt_mul_of_pos_left hP (by positivity)
    _ = Q ^ ((m + 1) * m + (m + 1 + 1) + 2 * m ^ 2) := by rw [← pow_add]
    _ ≤ Q ^ (3 * ((m + 1) * m)) := Nat.pow_le_pow_right hQ0 (by nlinarith)

theorem numerator_lt {t : StatedLieTag} {n r f : ℕ} (hadm : StatedLieAdmissible t n r f)
    (hr2 : r ≠ 2) : lieOrderNumerator t n (r ^ f) < (r ^ f) ^ (3 * lieSylowExponent t n) := by
  have hr : r.Prime := hadm.1
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hQ3 : 3 ≤ r ^ f := hr3.trans (Nat.le_self_pow (by have := hadm.2.1; omega) r)
  obtain ⟨-, -, hcase⟩ := hadm
  generalize r ^ f = Q at hQ3 ⊢
  have hQ : 2 ≤ Q := by omega
  have hQ1 : 1 < Q := by omega
  have h1 : ∀ i, Q ^ i - 1 ≤ Q ^ i := pow_sub_one_le
  have h2 : ∀ i, Q ^ i + 1 ≤ Q ^ (i + 1) := pow_add_one_le_pow_succ hQ
  cases t with
  | PSL => exact psl_lt hQ hcase.1
  | PSU => exact psu_lt hQ hcase.1
  | PSp => exact psp_lt hQ (by have := hcase.1; omega)
  | POmegaOdd => exact psp_lt hQ (by have := hcase.1; omega)
  | POmegaPlus =>
    simp only [lieOrderNumerator, lieSylowExponent]
    exact omega_lt hQ hcase ((h1 n).trans (Nat.pow_le_pow_right (by omega) (by omega)))
  | POmegaMinus =>
    simp only [lieOrderNumerator, lieSylowExponent]
    exact omega_lt hQ hcase (h2 n)
  | G2 =>
    simp only [lieOrderNumerator, lieSylowExponent]
    exact (mul_le_pow_add (mul_le_pow_add le_rfl (h1 6)) (h1 2)).trans_lt
      (Nat.pow_lt_pow_right hQ1 (by norm_num))
  | F4 =>
    simp only [lieOrderNumerator, lieSylowExponent]
    exact (mul_le_pow_add (mul_le_pow_add (mul_le_pow_add (mul_le_pow_add le_rfl (h1 12))
      (h1 8)) (h1 6)) (h1 2)).trans_lt (Nat.pow_lt_pow_right hQ1 (by norm_num))
  | E6 =>
    simp only [lieOrderNumerator, lieSylowExponent]
    exact (mul_le_pow_add (mul_le_pow_add (mul_le_pow_add (mul_le_pow_add (mul_le_pow_add
      (mul_le_pow_add le_rfl (h1 12)) (h1 9)) (h1 8)) (h1 6)) (h1 5)) (h1 2)).trans_lt
      (Nat.pow_lt_pow_right hQ1 (by norm_num))
  | E7 =>
    simp only [lieOrderNumerator, lieSylowExponent]
    exact (mul_le_pow_add (mul_le_pow_add (mul_le_pow_add (mul_le_pow_add (mul_le_pow_add
      (mul_le_pow_add (mul_le_pow_add le_rfl (h1 18)) (h1 14)) (h1 12)) (h1 10)) (h1 8))
      (h1 6)) (h1 2)).trans_lt (Nat.pow_lt_pow_right hQ1 (by norm_num))
  | E8 =>
    rw [show lieSylowExponent .E8 n = 120 from rfl,
      show lieOrderNumerator .E8 n Q = Q ^ 120 * (Q ^ 30 - 1) * (Q ^ 24 - 1) * (Q ^ 20 - 1) *
        (Q ^ 18 - 1) * (Q ^ 14 - 1) * (Q ^ 12 - 1) * (Q ^ 8 - 1) * (Q ^ 2 - 1) from rfl]
    exact lt_pow_of_le_pow hQ1 (mul_le_pow_add (mul_le_pow_add (mul_le_pow_add
      (mul_le_pow_add (mul_le_pow_add (mul_le_pow_add (mul_le_pow_add (mul_le_pow_add le_rfl
      (h1 30)) (h1 24)) (h1 20)) (h1 18)) (h1 14)) (h1 12)) (h1 8)) (h1 2)) (by norm_num)
  | twistedE6 =>
    simp only [lieOrderNumerator, lieSylowExponent]
    exact (mul_le_pow_add (mul_le_pow_add (mul_le_pow_add (mul_le_pow_add (mul_le_pow_add
      (mul_le_pow_add le_rfl (h1 12)) (h2 9)) (h1 8)) (h1 6)) (h2 5)) (h1 2)).trans_lt
      (Nat.pow_lt_pow_right hQ1 (by norm_num))
  | trialityD4 =>
    simp only [lieOrderNumerator, lieSylowExponent]
    have h3 : Q ^ 8 + Q ^ 4 + 1 ≤ Q ^ 9 := by
      have h4 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ (by omega)
      have h8 : Q ^ 8 = Q ^ 4 * Q ^ 4 := by ring
      have h9 : Q ^ 9 = Q ^ 4 * Q ^ 4 * Q := by ring
      rw [h8, h9]
      nlinarith
    exact (mul_le_pow_add (mul_le_pow_add (mul_le_pow_add le_rfl h3) (h1 6)) (h1 2)).trans_lt
      (Nat.pow_lt_pow_right hQ1 (by norm_num))
  | twistedB2 => exact absurd hcase.2.1 hr2
  | twistedG2 =>
    simp only [lieOrderNumerator, lieSylowExponent]
    have h3 : Q - 1 ≤ Q ^ 1 := by rw [pow_one]; exact Nat.sub_le _ _
    exact (mul_le_pow_add (mul_le_pow_add le_rfl (h2 3)) h3).trans_lt
      (Nat.pow_lt_pow_right hQ1 (by norm_num))
  | twistedF4 => exact absurd hcase.2.1 hr2
  | Tits => exact absurd hcase.2.1 hr2

theorem divisor_pos {t : StatedLieTag} {n Q : ℕ} (hQ : 2 ≤ Q) : 0 < lieOrderDivisor t n Q := by
  cases t <;> simp only [lieOrderDivisor] <;>
    first
    | exact Nat.gcd_pos_of_pos_right _ (by omega)
    | exact Nat.gcd_pos_of_pos_left _ (by norm_num)
    | norm_num

theorem pslTwoOddCharacteristicFact_holds :
    PSLTwoOddCharacteristicFact := by
  intro X _ p m t n r f hp hp2 h7 hr2 hX hL
  by_contra hrp
  have hadm := admissible_of_lieModel' hL
  obtain ⟨-, hmul, hfac⟩ := CatLeafProof.lieOrderFormulasInput X t n r f hadm hL
  have hr : r.Prime := hadm.1
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  set q := p ^ m with hq
  set N := lieSylowExponent t n with hN
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = r ^ f := ⟨_, rfl⟩
  rw [← hQdef] at hmul
  have hQ3 : 3 ≤ Q := hQdef ▸ hr3.trans (Nat.le_self_pow (by have := hadm.2.1; omega) r)
  obtain ⟨-, -, -, F, _, _, hF, ⟨e⟩⟩ := exists_psl2_of_lieModel hX
  have hXc : Nat.card X = q * ((q ^ 2 - 1) / 2) := by
    rw [Nat.card_congr e.toEquiv, SectionRank.OddCover.card_psl_two hp hp2 hF]
  obtain ⟨u, hu⟩ : ∃ u, q = u + 7 := ⟨q - 7, by omega⟩
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [hu, show u + 7 - 1 = u + 6 by omega]
    exact Nat.sub_eq_of_eq_add (by ring)
  have hqodd : Odd q := (hp.odd_of_ne_two hp2).pow
  have hev : 2 ∣ q ^ 2 - 1 := by
    obtain ⟨k, hk⟩ := hqodd
    rw [hsq, hk, Nat.add_sub_cancel]
    exact Dvd.intro (k * (2 * k + 1 + 1)) (by ring)
  have hX2 : Nat.card X * 2 = q * (q ^ 2 - 1) := by
    rw [hXc, mul_assoc, Nat.div_mul_cancel hev]
  have hrX : Q ^ N ∣ Nat.card X := by
    have h1 := Nat.ordProj_dvd (Nat.card X) r
    rw [hfac] at h1
    rwa [hQdef, ← pow_mul, mul_comm f]
  have hcop : Nat.Coprime (Q ^ N) q := by
    rw [hQdef]
    exact Nat.Coprime.pow_left N (Nat.Coprime.pow f m ((Nat.coprime_primes hr hp).mpr hrp))
  have hdvd : Q ^ N ∣ (q - 1) * (q + 1) := by
    have h1 : Q ^ N ∣ q * ((q - 1) * (q + 1)) := by
      rw [← hsq, ← hX2]
      exact Dvd.dvd.mul_right hrX 2
    exact hcop.dvd_of_dvd_mul_left h1
  have hQodd : Odd (Q ^ N) := by
    rw [hQdef]
    exact ((hr.odd_of_ne_two hr2).pow).pow
  have h2c : Nat.Coprime 2 (Q ^ N) := Nat.coprime_two_left.mpr hQodd
  have h2Q : 2 * Q ^ N ≤ q + 1 := by
    by_cases hr1 : r ∣ q + 1
    ·
      have hr1' : ¬ r ∣ q - 1 := by
        intro h
        have h2 : r ∣ (q + 1) - (q - 1) := Nat.dvd_sub hr1 h
        rw [show (q + 1) - (q - 1) = 2 by omega] at h2
        exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)
      have hc : Nat.Coprime (Q ^ N) (q - 1) := by
        rw [hQdef]
        exact Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _
          ((Nat.Prime.coprime_iff_not_dvd hr).mpr hr1'))
      have h1 : Q ^ N ∣ q + 1 := hc.dvd_of_dvd_mul_left hdvd
      have h2 : 2 ∣ q + 1 := by obtain ⟨k, hk⟩ := hqodd; exact ⟨k + 1, by omega⟩
      exact Nat.le_of_dvd (by omega) (h2c.mul_dvd_of_dvd_of_dvd h2 h1)
    · have hc : Nat.Coprime (Q ^ N) (q + 1) := by
        rw [hQdef]
        exact Nat.Coprime.pow_left _ (Nat.Coprime.pow_left _
          ((Nat.Prime.coprime_iff_not_dvd hr).mpr hr1))
      have h1 : Q ^ N ∣ q - 1 := hc.dvd_of_dvd_mul_right hdvd
      have h2 : 2 ∣ q - 1 := by obtain ⟨k, hk⟩ := hqodd; exact ⟨k, by omega⟩
      exact (Nat.le_of_dvd (by omega) (h2c.mul_dvd_of_dvd_of_dvd h2 h1)).trans (by omega)
  have hlt : Nat.card X < Q ^ (3 * N) := by
    calc Nat.card X ≤ Nat.card X * lieOrderDivisor t n Q :=
          Nat.le_mul_of_pos_right _ (divisor_pos (by omega))
      _ = lieOrderNumerator t n Q := hmul
      _ < Q ^ (3 * N) := hQdef ▸ numerator_lt hadm hr2
  have h8 : (q + 1) ^ 3 ≤ 4 * (q * (q ^ 2 - 1)) := by
    rw [hsq, hu, show u + 7 - 1 = u + 6 by omega]
    ring_nf
    omega
  have hcube : 8 * Q ^ (3 * N) ≤ 8 * Nat.card X := by
    calc 8 * Q ^ (3 * N) = 2 ^ 3 * (Q ^ N) ^ 3 := by rw [← pow_mul, mul_comm N 3]; norm_num
      _ = (2 * Q ^ N) ^ 3 := (mul_pow 2 (Q ^ N) 3).symm
      _ ≤ (q + 1) ^ 3 := Nat.pow_le_pow_left h2Q 3
      _ ≤ 4 * (q * (q ^ 2 - 1)) := h8
      _ = 8 * Nat.card X := by rw [← hX2]; ring
  omega

end OddChar

end CFSG.ComponentClassification.HarrisLit.N36
