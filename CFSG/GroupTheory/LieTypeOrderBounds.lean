module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588D3
public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Timmesfeld.Orders

theorem two_pow_le_of_dvd_ordA_one {p N : ℕ} (hp : Odd p) (hp3 : 3 ≤ p)
    (h : 2 ^ N ∣ ordA 1 p) : 2 ^ N ≤ p + 1 := by
  obtain ⟨a, rfl⟩ := hp
  rcases N with _ | N
  · simp
  have h2 := CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one (q := 2 * a + 1) ⟨a, rfl⟩
  have hsq : (2 * a + 1) ^ 2 - 1 = 2 * 2 * (a * (a + 1)) := by
    have : (2 * a + 1) ^ 2 = 2 * 2 * (a * (a + 1)) + 1 := by ring
    omega
  have hord : ordA 1 (2 * a + 1) = 2 * ((2 * a + 1) * (a * (a + 1))) := by
    rw [hsq] at h2
    have : 2 * ordA 1 (2 * a + 1) = 2 * (2 * ((2 * a + 1) * (a * (a + 1)))) := by
      rw [h2]
      ring
    omega
  rw [hord, pow_succ, mul_comm (2 ^ N) 2] at h
  have h1 : 2 ^ N ∣ (2 * a + 1) * (a * (a + 1)) := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  have hc : Nat.Coprime (2 ^ N) (2 * a + 1) :=
    Nat.Coprime.pow_left N (Nat.coprime_two_left.mpr ⟨a, rfl⟩)
  have h1' : 2 ^ N ∣ a * (a + 1) := hc.dvd_of_dvd_mul_left h1
  have hle : 2 ^ N ≤ a + 1 := by
    rcases Nat.even_or_odd a with ha | ha
    · have hc' : Nat.Coprime (2 ^ N) (a + 1) :=
        Nat.Coprime.pow_left N (Nat.coprime_two_left.mpr ha.add_one)
      have := Nat.le_of_dvd (by omega) (hc'.dvd_of_dvd_mul_right h1')
      omega
    · have hc' : Nat.Coprime (2 ^ N) a := Nat.Coprime.pow_left N (Nat.coprime_two_left.mpr ha)
      exact Nat.le_of_dvd (by omega) (hc'.dvd_of_dvd_mul_left h1')
  rw [pow_succ]
  omega

theorem ordA_one_ge {p M : ℕ} (hp : Odd p) (hM : M ≤ p + 1) :
    (M - 1) * ((M - 1) ^ 2 - 1) ≤ 2 * ordA 1 p := by
  rw [CFSG.LocalAnalysis.UniquenessCase.UC6.N588.two_mul_ordA_one hp]
  have h1 : M - 1 ≤ p := by omega
  exact Nat.mul_le_mul h1 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h1 2) 1)

theorem ordA_one_ne_of_two_pow {p b N : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hdvd : 2 ^ N ∣ b)
    (hlt : 2 * b < (2 ^ N - 1) * ((2 ^ N - 1) ^ 2 - 1)) : ordA 1 p ≠ b := by
  rintro rfl
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have := ordA_one_ge hodd (two_pow_le_of_dvd_ordA_one hodd (by omega) hdvd)
  omega

theorem two_mul_lt_of_le {b M c : ℕ} (hb : b ≤ M * ((M - 1) * c)) (hc : 2 * c + 2 < M) :
    2 * b < (M - 1) * ((M - 1) ^ 2 - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 2 := ⟨M - 2, by omega⟩
  have hM : (k + 2 - 1) ^ 2 - 1 = (k + 2) * k := by
    rw [show k + 2 - 1 = k + 1 by omega]
    have : (k + 1) ^ 2 = (k + 2) * k + 1 := by ring
    omega
  rw [hM]
  calc 2 * b ≤ 2 * ((k + 2) * ((k + 2 - 1) * c)) := Nat.mul_le_mul_left 2 hb
    _ = (k + 2 - 1) * ((k + 2) * (2 * c)) := by ring
    _ < (k + 2 - 1) * ((k + 2) * k) :=
        Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left (by omega) (by omega)) (by omega)

theorem two_mul_pow_add_two_lt {q k m : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) (hkm : k + 2 ≤ m) :
    2 * q ^ k + 2 < q ^ m := by
  have h1 : q ^ k * q ^ 2 ≤ q ^ m := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by omega) hkm
  have h2 : 4 ≤ q ^ 2 := by nlinarith
  have h3 : 2 ≤ q ^ k := le_trans hq (Nat.le_self_pow (by omega) q)
  nlinarith

theorem ordBC_two_two_pow {e : ℕ} (he : 1 ≤ e) :
    ordBC 2 (2 ^ e) = (2 ^ e) ^ 4 * (((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 4 - 1)) := by
  have h : Nat.gcd 2 (2 ^ e - 1) = 1 :=
    Nat.coprime_two_left.mpr (odd_two_pow_sub_one he)
  unfold ordBC
  rw [h, Nat.div_one, show 2 * 2 = 4 by rfl, show Finset.Icc 1 2 = {1, 2} by rfl,
    Finset.prod_pair (by norm_num)]

theorem two_part_ordBC_two {e : ℕ} (he : 1 ≤ e) :
    ∃ r, Odd r ∧ ordBC 2 (2 ^ e) = 2 ^ (e * 4) * r :=
  (profile_ordBC (n := 2) he).two

theorem ordBC_two_small {e : ℕ} (he : 1 ≤ e) :
    2 * ordBC 2 (2 ^ e) < (2 ^ (e * 4) - 1) * ((2 ^ (e * 4) - 1) ^ 2 - 1) := by
  rw [ordBC_two_two_pow he, pow_mul]
  have hq2 : 2 ≤ 2 ^ e := Nat.one_lt_two_pow (by omega)
  generalize 2 ^ e = q at hq2 ⊢
  refine two_mul_lt_of_le (c := q ^ 2) ?_ (two_mul_pow_add_two_lt hq2 (by norm_num) le_rfl)
  rw [mul_comm (q ^ 2 - 1)]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

theorem two_part_ordTwistedA_two {e : ℕ} (he : 1 ≤ e) :
    ∃ r, Odd r ∧ ordTwistedA 2 (2 ^ e) = 2 ^ (e * 3) * r := by
  obtain ⟨r, hr, hm⟩ := (profile_ordTwistedA (n := 2) (by norm_num) he).two
  exact ⟨r, hr, by simpa [show 2 * (2 + 1) / 2 = 3 by norm_num] using hm⟩

private theorem ordTwistedA_two_le {q : ℕ} (hq : 1 ≤ q) :
    ordTwistedA 2 q ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  unfold ordTwistedA
  rw [show 2 * (2 + 1) / 2 = 3 by norm_num,
    show Finset.Icc 2 (2 + 1) = {2, 3} by decide, Finset.prod_pair (by norm_num)]
  have h2 : (((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat) = q ^ 2 - 1 := by
    rw [show ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub (Nat.one_le_pow 2 q hq)]; ring]
    exact Int.toNat_natCast _
  have h3 : (((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat) = q ^ 3 + 1 := by
    rw [show ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast _
  rw [h2, h3]
  exact Nat.div_le_self _ _

theorem ordTwistedA_two_small {e : ℕ} (he : 2 ≤ e) :
    2 * ordTwistedA 2 (2 ^ e) < (2 ^ (e * 3) - 1) * ((2 ^ (e * 3) - 1) ^ 2 - 1) := by
  rw [pow_mul]
  have hq4 : 4 ≤ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  generalize 2 ^ e = q at hq4 ⊢
  have hq1 : 1 ≤ q := by omega
  refine two_mul_lt_of_le (c := q ^ 2) ?_ ?_
  · refine (ordTwistedA_two_le hq1).trans (Nat.mul_le_mul_left _ ?_)
    have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q hq1
    have h2 : 1 ≤ q ^ 3 := Nat.one_le_pow 3 q hq1
    zify [h1, h2]
    nlinarith [hq4]
  · nlinarith [hq4]

end CFSG.GroupTheory
