module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdEven

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

namespace LinCase

open CFSG.Blueprint

theorem linord_three_dvd_two_pow_sq_sub_one (f : ℕ) : 3 ∣ 2 ^ (2 * f) - 1 := by
  have h4 : 2 ^ (2 * f) = 4 ^ f := by rw [pow_mul]; norm_num
  rw [h4]
  have h := Nat.sub_dvd_pow_sub_pow 4 1 f
  rw [one_pow] at h
  exact h

theorem linord_key (a A g m : ℕ) (ha3 : 3 ≤ a)
    (hA : A * g = (a + 1) ^ 3 * (a * (a + 2)) * ((a + 1) ^ 3 + 1))
    (hL : A ^ 2 * m * 3 = ((a + 1) ^ 2) ^ 3 * (a * (a + 2) * ((a + 1) ^ 2 + 1)) *
      (a * (a ^ 2 + 3 * a + 3) * ((a + 1) ^ 3 + 1))) :
    (a + 2) ^ 2 * (a ^ 2 + a + 1) * (3 * m) =
      g ^ 2 * ((a ^ 2 + 2 * a + 2) * (a ^ 2 + 3 * a + 3)) := by
  have hA' : (A : ℤ) * g =
      ((a : ℤ) + 1) ^ 3 * ((a : ℤ) * ((a : ℤ) + 2)) * (((a : ℤ) + 1) ^ 3 + 1) := by
    exact_mod_cast hA
  have hL' : (A : ℤ) ^ 2 * m * 3 =
      (((a : ℤ) + 1) ^ 2) ^ 3 * ((a : ℤ) * ((a : ℤ) + 2) * (((a : ℤ) + 1) ^ 2 + 1)) *
        ((a : ℤ) * ((a : ℤ) ^ 2 + 3 * a + 3) * (((a : ℤ) + 1) ^ 3 + 1)) := by
    exact_mod_cast hL
  have ha0 : (a : ℤ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have ha1 : (a : ℤ) + 1 ≠ 0 := by omega
  have ha2 : (a : ℤ) + 2 ≠ 0 := by omega
  have ha4 : (a : ℤ) ^ 2 + a + 1 ≠ 0 := by positivity
  have hK : ((a : ℤ) + 1) ^ 6 * (a : ℤ) ^ 2 * ((a : ℤ) + 2) ^ 2 * ((a : ℤ) ^ 2 + a + 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero 6 ha1) (pow_ne_zero 2 ha0))
      (pow_ne_zero 2 ha2)) ha4
  have hKPQ : ((a : ℤ) + 1) ^ 6 * (a : ℤ) ^ 2 * ((a : ℤ) + 2) ^ 2 * ((a : ℤ) ^ 2 + a + 1) *
      (((a : ℤ) + 2) ^ 2 * ((a : ℤ) ^ 2 + a + 1) * (3 * m)) =
      ((a : ℤ) + 1) ^ 6 * (a : ℤ) ^ 2 * ((a : ℤ) + 2) ^ 2 * ((a : ℤ) ^ 2 + a + 1) *
      ((g : ℤ) ^ 2 * (((a : ℤ) ^ 2 + 2 * a + 2) * ((a : ℤ) ^ 2 + 3 * a + 3))) := by
    linear_combination (g : ℤ) ^ 2 * hL' - 3 * (m : ℤ) *
      ((A : ℤ) * g + ((a : ℤ) + 1) ^ 3 * ((a : ℤ) * ((a : ℤ) + 2)) * (((a : ℤ) + 1) ^ 3 + 1)) * hA'
  have hPQ := mul_left_cancel₀ hK hKPQ
  exact_mod_cast hPQ

theorem linord_contra (a g m : ℕ) (ha3 : 3 ≤ a) (ha_odd : a % 2 = 1) (hg3 : g ∣ 3)
    (hgpos : 0 < g)
    (h : (a + 2) ^ 2 * (a ^ 2 + a + 1) * (3 * m) =
      g ^ 2 * ((a ^ 2 + 2 * a + 2) * (a ^ 2 + 3 * a + 3))) :
    False := by
  have hc1 : Nat.Coprime (a + 2) (a ^ 2 + 2 * a + 2) := by
    have h2 : ¬ 2 ∣ a + 2 := by omega
    have hc2 : Nat.Coprime (a + 2) 2 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
    rw [show a ^ 2 + 2 * a + 2 = 2 + a * (a + 2) by ring, Nat.coprime_add_mul_right_right]
    exact hc2
  have hc3 : Nat.Coprime (a + 2) (a ^ 2 + 3 * a + 3) := by
    rw [show a ^ 2 + 3 * a + 3 = 1 + (a + 1) * (a + 2) by ring, Nat.coprime_add_mul_right_right]
    exact Nat.coprime_one_right _
  have hcop : Nat.Coprime ((a + 2) ^ 2) ((a ^ 2 + 2 * a + 2) * (a ^ 2 + 3 * a + 3)) :=
    Nat.Coprime.mul_right (Nat.Coprime.pow_left 2 hc1) (Nat.Coprime.pow_left 2 hc3)
  have hdvd : (a + 2) ^ 2 ∣ g ^ 2 * ((a ^ 2 + 2 * a + 2) * (a ^ 2 + 3 * a + 3)) :=
    ⟨(a ^ 2 + a + 1) * (3 * m), by rw [← h]; ring⟩
  have h5 : (a + 2) ^ 2 ∣ g ^ 2 := hcop.dvd_of_dvd_mul_right hdvd
  have h6 : a + 2 ∣ g := (Nat.pow_dvd_pow_iff two_ne_zero).mp h5
  have h7 : a + 2 ≤ g := Nat.le_of_dvd hgpos h6
  have h8 : g ≤ 3 := Nat.le_of_dvd (by norm_num) hg3
  omega

theorem card_lieModel_PSL3 {G : Type} [Group G] {e : ℕ} (h : LieModel G .PSL 3 2 e) :
    Nat.card G * Nat.gcd 3 (2 ^ e - 1) =
      (2 ^ e) ^ 3 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 - 1) := by
  have hcard := CFSG.ComponentClassification.GSThmB.Catalog7Std.card_of_lieModel_PSL
    (n := 3) (e := e) (by norm_num) h
  have hexp : 3 * (3 - 1) / 2 = 3 := by norm_num
  have hprod : (∏ j ∈ Finset.Icc 2 3, ((2 ^ e) ^ j - 1)) =
      ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 - 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3)]
  rw [hexp, hprod] at hcard
  have h2 : 2 ^ e - 1 ∣ (2 ^ e) ^ 3 - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow (2 ^ e) 1 3
    rwa [one_pow] at h
  have h3 : Nat.gcd 3 (2 ^ e - 1) ∣ (2 ^ e) ^ 3 - 1 :=
    dvd_trans (Nat.gcd_dvd_right 3 (2 ^ e - 1)) h2
  have hdvd : Nat.gcd 3 (2 ^ e - 1) ∣
      (2 ^ e) ^ 3 * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left h3 _) _
  rw [hcard, Nat.div_mul_cancel hdvd, mul_assoc]

theorem card_lieModel_PSU3 {G : Type} [Group G] {e : ℕ} (he : 1 ≤ e) (h : LieModel G .PSU 3 2 e) :
    Nat.card G * Nat.gcd 3 (2 ^ e + 1) =
      (2 ^ e) ^ 3 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1) := by
  have hcard := CFSG.ComponentClassification.GSThmB.Catalog7Std.card_of_lieModel_PSU
    (n := 3) (e := e) (by norm_num) he h
  have hexp : 3 * (3 - 1) / 2 = 3 := by norm_num
  have hx2 : 1 ≤ (2 ^ e) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have c2 : (((2 ^ e : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = (2 ^ e) ^ 2 - 1 := by
    have h' : (((2 ^ e : ℕ) : ℤ) ^ 2 - (-1) ^ 2) = (((2 ^ e) ^ 2 - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub hx2]
      push_cast
      ring
    rw [h', Int.toNat_natCast]
  have c3 : (((2 ^ e : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = (2 ^ e) ^ 3 + 1 := by
    have h' : (((2 ^ e : ℕ) : ℤ) ^ 3 - (-1) ^ 3) = (((2 ^ e) ^ 3 + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [h', Int.toNat_natCast]
  have hprod : (∏ i ∈ Finset.Icc 2 3, (((2 ^ e : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) =
      ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1) := by
    rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num : (2 : ℕ) ≠ 3)]
    simp only [c2, c3]
  rw [hexp, hprod] at hcard
  have h2 : 2 ^ e + 1 ∣ (2 ^ e) ^ 3 + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow (2 ^ e) 1 (by decide : Odd 3)
    rwa [one_pow] at h
  have h3 : Nat.gcd 3 (2 ^ e + 1) ∣ (2 ^ e) ^ 3 + 1 :=
    dvd_trans (Nat.gcd_dvd_right 3 (2 ^ e + 1)) h2
  have hdvd : Nat.gcd 3 (2 ^ e + 1) ∣
      (2 ^ e) ^ 3 * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left h3 _) _
  rw [hcard, Nat.div_mul_cancel hdvd, mul_assoc]

theorem not_card_sq_dvd {f : ℕ} (hf : 2 ≤ f) {A L : ℕ}
    (hA : A * Nat.gcd 3 (2 ^ f + 1) = (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1))
    (hL : L * Nat.gcd 3 (2 ^ (2 * f) - 1) =
      (2 ^ (2 * f)) ^ 3 * ((2 ^ (2 * f)) ^ 2 - 1) * ((2 ^ (2 * f)) ^ 3 - 1)) :
    ¬ A ^ 2 ∣ L := by
  rintro ⟨m, rfl⟩
  rw [Nat.gcd_eq_left (linord_three_dvd_two_pow_sq_sub_one f)] at hL
  obtain ⟨g, hg⟩ : ∃ g, Nat.gcd 3 (2 ^ f + 1) = g := ⟨_, rfl⟩
  rw [hg] at hA
  have hg3 : g ∣ 3 := by
    rw [← hg]
    exact Nat.gcd_dvd_left 3 (2 ^ f + 1)
  have hgpos : 0 < g := by
    rw [← hg]
    exact Nat.gcd_pos_of_pos_left _ (by norm_num)
  obtain ⟨a, ha⟩ : ∃ a, 2 ^ f = a + 1 := ⟨2 ^ f - 1, by
    have : 0 < 2 ^ f := by positivity
    omega⟩
  have hq4 : 4 ≤ 2 ^ f := by
    have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hf
    simpa using h
  have hdvd2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  rw [ha] at hdvd2 hq4
  have ha3 : 3 ≤ a := by omega
  have ha_odd : a % 2 = 1 := by omega
  have h2f : 2 ^ (2 * f) = (a + 1) ^ 2 := by rw [pow_mul', ha]
  rw [h2f] at hL
  rw [ha] at hA
  have e1 : (a + 1) ^ 2 - 1 = a * (a + 2) := Nat.sub_eq_of_eq_add (by ring)
  have e2 : ((a + 1) ^ 2) ^ 2 - 1 = a * (a + 2) * ((a + 1) ^ 2 + 1) :=
    Nat.sub_eq_of_eq_add (by ring)
  have e3 : ((a + 1) ^ 2) ^ 3 - 1 = a * (a ^ 2 + 3 * a + 3) * ((a + 1) ^ 3 + 1) :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [e1] at hA
  rw [e2, e3] at hL
  exact linord_contra a g m ha3 ha_odd hg3 hgpos (linord_key a A g m ha3 hA hL)

end LinCase

end CFSG.LocalAnalysis.EvenBN.U5
