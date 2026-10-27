module

public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem exists_torsion_moved {F : Type} [Field F] [Finite F] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he : 1 ≤ e) (σ : F ≃+* F) (hcard : Nat.card F = (p ^ e) ^ p)
    (hfix : Nat.card (semilinearFixedSubfield σ) = p ^ e) :
    ∃ (r : ℕ) (c : Fˣ), r.Prime ∧ r ≠ 2 ∧ r ≠ p ∧ c ^ r = 1 ∧ σ (c : F) ≠ (c : F) := by
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
  set Φ : ℕ := ∑ i ∈ Finset.range p, q0 ^ i with hΦ
  have hΦodd : Odd Φ := by
    have h1 : ∀ i ∈ Finset.range p, q0 ^ i % 2 = 1 := fun i _ => Nat.odd_iff.mp hq0odd.pow
    have h2 : Φ % 2 = p % 2 := by
      rw [hΦ, Finset.sum_nat_mod, Finset.sum_congr rfl h1]
      simp
    rw [Nat.odd_iff, h2]
    exact Nat.odd_iff.mp hpodd
  have hΦgt : 1 < Φ := by
    have : 1 + q0 ≤ Φ := by
      have hp2' : 2 ≤ p := hp.two_le
      obtain ⟨m, hm⟩ : ∃ m, p = m + 2 := ⟨p - 2, by omega⟩
      rw [hΦ, hm, Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [zero_add, pow_zero, pow_one]
      omega
    omega
  have hgeom : Φ * (q0 - 1) = q0 ^ p - 1 := by
    have h1 : (Φ : ℤ) * ((q0 : ℤ) - 1) = (q0 : ℤ) ^ p - 1 := by
      rw [hΦ]
      push_cast
      exact geom_sum_mul _ _
    have h2 : 1 ≤ q0 := by omega
    have h3 : 1 ≤ q0 ^ p := Nat.one_le_pow _ _ (by omega)
    zify [h2, h3]
    exact h1
  have hr : (Nat.minFac Φ).Prime := Nat.minFac_prime (by omega)
  set r := Nat.minFac Φ with hrdef
  have hrΦ : r ∣ Φ := Nat.minFac_dvd Φ
  have hr2 : r ≠ 2 := by
    rintro h2
    rw [h2] at hrΦ
    exact (Nat.not_even_iff_odd.mpr hΦodd) (even_iff_two_dvd.mpr hrΦ)
  have hq : Nat.card F = q0 ^ p := hcard
  have hrq1 : r ∣ Nat.card F - 1 := by
    rw [hq, ← hgeom]
    exact hrΦ.mul_right _
  have hrp : r ≠ p := by
    rintro h
    have h1 : p ∣ Nat.card F - 1 := h ▸ hrq1
    have h2 : p ∣ Nat.card F := by
      rw [hq]
      exact hpq0.trans (dvd_pow_self q0 hp.ne_zero)
    have h3 : p ∣ 1 := by
      have := Nat.dvd_sub h2 h1
      have h4 : 1 ≤ Nat.card F := Nat.card_pos
      rwa [Nat.sub_sub_self h4] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
  have hrq0 : ¬ r ∣ q0 - 1 := by
    intro hdvd
    have h1 : (q0 : ZMod r) = 1 := by
      have : ((q0 - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      rw [Nat.cast_sub (by omega)] at this
      simpa [sub_eq_zero] using this
    have h2 : (Φ : ZMod r) = (p : ZMod r) := by
      rw [hΦ]
      push_cast
      simp [h1]
    have h3 : (Φ : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hrΦ
    have h4 : r ∣ p := (ZMod.natCast_eq_zero_iff _ _).mp (h2 ▸ h3)
    have h5 : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp h4
    exact hrp h5
  have : Fact r.Prime := ⟨hr⟩
  have hrcard : r ∣ Nat.card Fˣ := by
    rw [Nat.card_units]
    exact hrq1
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' r hrcard
  refine ⟨r, c, hr, hr2, hrp, hc ▸ pow_orderOf_eq_one c, fun hσ => ?_⟩
  have hmem : (c : F) ∈ semilinearFixedSubfield σ := by
    rw [RingHom.mem_eqLocusField]
    simpa using hσ
  have hpow : ((⟨(c : F), hmem⟩ : semilinearFixedSubfield σ)) ^ q0 = ⟨(c : F), hmem⟩ := by
    have := Fintype.ofFinite (semilinearFixedSubfield σ)
    have h1 := FiniteField.pow_card (⟨(c : F), hmem⟩ : semilinearFixedSubfield σ)
    have h2 : Fintype.card (semilinearFixedSubfield σ) = q0 := by
      rw [← Nat.card_eq_fintype_card, hfix]
    rwa [h2] at h1
  have hpowF : (c : F) ^ q0 = (c : F) := congrArg Subtype.val hpow
  have hpowU : c ^ q0 = c := Units.ext (by simpa using hpowF)
  have h1 : c ^ (q0 - 1) = 1 := by
    have h2 : c ^ (q0 - 1) * c = 1 * c := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hpowU, one_mul]
    exact mul_right_cancel h2
  exact hrq0 (hc ▸ orderOf_dvd_of_pow_eq_one h1)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
