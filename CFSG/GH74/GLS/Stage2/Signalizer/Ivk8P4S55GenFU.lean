module

public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem exists_prime_alt_factor {p q0 : ℕ} (hp : p.Prime) (hpodd : Odd p) (hq0odd : Odd q0)
    (hq0ge : 3 ≤ q0) (hpq0 : p ∣ q0) :
    ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ p ∧ r ∣ q0 ^ p + 1 ∧ ¬ r ∣ q0 + 1 ∧ ¬ r ∣ q0 - 1 := by
  classical
  set Ψ : ℤ := ∑ i ∈ Finset.range p, (-(q0 : ℤ)) ^ i with hΨ
  have hΨmul : Ψ * ((q0 : ℤ) + 1) = (q0 : ℤ) ^ p + 1 := by
    have h1 : (∑ i ∈ Finset.range p, (-(q0 : ℤ)) ^ i) * (-(q0 : ℤ) - 1) =
        (-(q0 : ℤ)) ^ p - 1 := geom_sum_mul _ _
    have h2 : (-(q0 : ℤ)) ^ p = -((q0 : ℤ) ^ p) := hpodd.neg_pow _
    rw [h2] at h1
    rw [hΨ]
    linarith
  have hΨodd : Odd Ψ := by
    have h1 : ∀ i ∈ Finset.range p, (-(q0 : ℤ)) ^ i % 2 = 1 := fun i _ => by
      have hq : Odd (q0 : ℤ) := by exact_mod_cast hq0odd
      exact Int.odd_iff.mp (hq.neg.pow)
    have h2 : Ψ % 2 = (p : ℤ) % 2 := by
      rw [hΨ, Finset.sum_int_mod, Finset.sum_congr rfl h1]
      simp
    rw [Int.odd_iff, h2]
    exact Int.odd_iff.mp (by exact_mod_cast hpodd)
  have hq1 : (0 : ℤ) < (q0 : ℤ) + 1 := by positivity
  have hq0p : (q0 : ℤ) < (q0 : ℤ) ^ p := by
    have hp2 : 2 ≤ p := hp.two_le
    calc (q0 : ℤ) = (q0 : ℤ) ^ 1 := (pow_one _).symm
      _ < (q0 : ℤ) ^ p := pow_lt_pow_right₀ (by exact_mod_cast (by omega : 1 < q0)) (by omega)
  have hΨgt : 1 < Ψ := by
    by_contra hle
    push Not at hle
    have h1 : Ψ * ((q0 : ℤ) + 1) ≤ 1 * ((q0 : ℤ) + 1) := mul_le_mul_of_nonneg_right hle hq1.le
    rw [hΨmul] at h1
    linarith
  obtain ⟨Ψ', hΨ'⟩ : ∃ Ψ' : ℕ, (Ψ' : ℤ) = Ψ := ⟨Ψ.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hΨ'gt : 1 < Ψ' := by
    have : (1 : ℤ) < Ψ' := hΨ' ▸ hΨgt
    exact_mod_cast this
  have hΨ'odd : Odd Ψ' := by
    have : Odd (Ψ' : ℤ) := hΨ' ▸ hΨodd
    exact_mod_cast this
  have hΨ'dvd : Ψ' ∣ q0 ^ p + 1 := by
    have h1 : (Ψ' : ℤ) ∣ (q0 : ℤ) ^ p + 1 := ⟨(q0 : ℤ) + 1, by rw [hΨ', hΨmul]⟩
    exact_mod_cast h1
  set r := Nat.minFac Ψ' with hrdef
  have hr : r.Prime := Nat.minFac_prime (by omega)
  have hrΨ : r ∣ Ψ' := Nat.minFac_dvd Ψ'
  have hr2 : r ≠ 2 := by
    rintro h2
    rw [h2] at hrΨ
    exact (Nat.not_even_iff_odd.mpr hΨ'odd) (even_iff_two_dvd.mpr hrΨ)
  have hrN : r ∣ q0 ^ p + 1 := hrΨ.trans hΨ'dvd
  have hrq1 : ¬ r ∣ q0 + 1 := by
    intro hdvd
    have h1 : (q0 : ZMod r) = -1 := by
      have : ((q0 + 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      push_cast at this
      exact eq_neg_of_add_eq_zero_left this
    have h2 : (Ψ' : ZMod r) = (p : ZMod r) := by
      have : ((Ψ' : ℤ) : ZMod r) = (Ψ : ZMod r) := by rw [hΨ']
      rw [hΨ] at this
      simp only [Int.cast_natCast, Int.cast_sum, Int.cast_pow, Int.cast_neg] at this
      rw [this, h1, neg_neg]
      simp
    have h3 : (Ψ' : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hrΨ
    have h4 : r ∣ p := (ZMod.natCast_eq_zero_iff _ _).mp (h2 ▸ h3)
    have h5 : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp h4
    have h6 : p ∣ q0 + 1 := h5 ▸ hdvd
    have h7 : p ∣ 1 := (Nat.dvd_add_right hpq0).mp h6
    exact hp.one_lt.ne' (Nat.dvd_one.mp h7)
  have hrp : r ≠ p := by
    rintro h
    have h1 : p ∣ q0 ^ p + 1 := h ▸ hrN
    have h2 : p ∣ q0 ^ p := hpq0.trans (dvd_pow_self q0 hp.ne_zero)
    have h3 : p ∣ 1 := (Nat.dvd_add_right h2).mp h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
  have hrq2 : ¬ r ∣ q0 - 1 := by
    intro hdvd
    have h1 : (q0 : ZMod r) = 1 := by
      have : ((q0 - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      rw [Nat.cast_sub (by omega)] at this
      simpa [sub_eq_zero] using this
    have h2 : ((q0 ^ p + 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hrN
    push_cast at h2
    rw [h1, one_pow] at h2
    have h3 : r ∣ 2 := by
      have : ((2 : ℕ) : ZMod r) = 0 := by simpa [one_add_one_eq_two] using h2
      exact (ZMod.natCast_eq_zero_iff _ _).mp this
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h3)
  exact ⟨r, hr, hr2, hrp, hrN, hrq1, hrq2⟩

theorem exists_torsion_moved_unitary {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (σ : K ≃+* K) (hcard : Nat.card K = ((p ^ e) ^ p) ^ 2)
    (hfix : Nat.card (semilinearFixedSubfield σ) = (p ^ e) ^ 2) :
    ∃ (r : ℕ) (c : Kˣ), r.Prime ∧ r ≠ 2 ∧ r ≠ p ∧ c ^ r = 1 ∧ c ^ ((p ^ e) ^ p + 1) = 1 ∧
      σ (c : K) ≠ (c : K) := by
  classical
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  set q0 : ℕ := p ^ e with hq0
  have hq0odd : Odd q0 := hpodd.pow
  have hq0ge : 3 ≤ q0 := by
    calc 3 ≤ p := hp3
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos he
  have hpq0 : p ∣ q0 := dvd_pow_self p (by omega)
  obtain ⟨r, hr, hr2, hrp, hrN, hrq1, hrq2⟩ :=
    exists_prime_alt_factor hp hpodd hq0odd hq0ge hpq0
  have : Fact r.Prime := ⟨hr⟩
  have hrcard : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hcard]
    have h1 : (q0 ^ p) ^ 2 - 1 = (q0 ^ p + 1) * (q0 ^ p - 1) := by
      have hq1 : 1 ≤ q0 ^ p := Nat.one_le_pow _ _ (by omega)
      zify [hq1, Nat.one_le_pow 2 (q0 ^ p) (by omega)]
      ring
    rw [h1]
    exact hrN.mul_right _
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' r hrcard
  refine ⟨r, c, hr, hr2, hrp, hc ▸ pow_orderOf_eq_one c, ?_, fun hσ => ?_⟩
  · exact orderOf_dvd_iff_pow_eq_one.mp (hc ▸ hrN)
  ·
    have hmem : (c : K) ∈ semilinearFixedSubfield σ := by
      rw [RingHom.mem_eqLocusField]
      simpa using hσ
    have hpow : ((⟨(c : K), hmem⟩ : semilinearFixedSubfield σ)) ^ (q0 ^ 2) =
        ⟨(c : K), hmem⟩ := by
      have := Fintype.ofFinite (semilinearFixedSubfield σ)
      have h1 := FiniteField.pow_card (⟨(c : K), hmem⟩ : semilinearFixedSubfield σ)
      have h2 : Fintype.card (semilinearFixedSubfield σ) = q0 ^ 2 := by
        rw [← Nat.card_eq_fintype_card, hfix]
      rwa [h2] at h1
    have hpowF : (c : K) ^ (q0 ^ 2) = (c : K) := congrArg Subtype.val hpow
    have hpowU : c ^ (q0 ^ 2) = c := Units.ext (by simpa using hpowF)
    have h1 : c ^ (q0 ^ 2 - 1) = 1 := by
      have h2 : c ^ (q0 ^ 2 - 1) * c = 1 * c := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega)), hpowU, one_mul]
      exact mul_right_cancel h2
    have h3 : r ∣ q0 ^ 2 - 1 := hc ▸ orderOf_dvd_of_pow_eq_one h1
    have h4 : q0 ^ 2 - 1 = (q0 + 1) * (q0 - 1) := by
      have hq1 : 1 ≤ q0 := by omega
      zify [hq1, Nat.one_le_pow 2 q0 (by omega)]
      ring
    rw [h4] at h3
    rcases (Nat.Prime.dvd_mul hr).mp h3 with h | h
    · exact hrq1 h
    · exact hrq2 h

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
