module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36OddChar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Reduce

public section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.HarrisLit.N36 CFSG.ComponentClassification.HarrisLit.N36.OddChar

theorem char_eq_of_pslTwo
    {X : Type} [Group X] {p m : ℕ} {t : StatedLieTag} {n r f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ m) (hr2 : r ≠ 2) (hX : Blueprint.LieModel X .PSL 2 p m)
    (hL : Blueprint.LieModel X t n r f) : r = p := by
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
  obtain ⟨u, hu⟩ : ∃ u, q = u + 5 := ⟨q - 5, by omega⟩
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [hu, show u + 5 - 1 = u + 4 by omega]
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
    rw [hsq, hu, show u + 5 - 1 = u + 4 by omega]
    ring_nf
    omega
  have hcube : 8 * Q ^ (3 * N) ≤ 8 * Nat.card X := by
    calc 8 * Q ^ (3 * N) = 2 ^ 3 * (Q ^ N) ^ 3 := by rw [← pow_mul, mul_comm N 3]; norm_num
      _ = (2 * Q ^ N) ^ 3 := (mul_pow 2 (Q ^ N) 3).symm
      _ ≤ (q + 1) ^ 3 := Nat.pow_le_pow_left h2Q 3
      _ ≤ 4 * (q * (q ^ 2 - 1)) := h8
      _ = 8 * Nat.card X := by rw [← hX2]; ring
  omega

end CFSG.ComponentClassification.HarrisLit.L35
