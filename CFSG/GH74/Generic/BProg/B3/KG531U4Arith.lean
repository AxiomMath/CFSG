module

public import CFSG.ClassicalInvolution.RouteD.TWRExoticArith

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace KG531U4Arith

theorem not_dvd_core (q : ℕ) (hq : q % 2 = 1) (h3 : 3 ≤ q) {n : ℕ}
    (hn : n = q ^ 2 * ((q ^ 2) ^ 2 - 1) / 2)
    (hD : (n * (2 * n)) ∣ q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) / Nat.gcd 4 (q + 1)) :
    False := by
  obtain ⟨a, ha⟩ : ∃ a, q ^ 2 = a + 1 :=
    ⟨q ^ 2 - 1, by have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega); omega⟩
  have hq3 : 3 * q ≤ q ^ 2 := by nlinarith
  have ha8 : 9 ≤ a + 1 := by nlinarith
  obtain ⟨m, hm⟩ : ∃ m, a + 2 = 2 * m := by
    have hodd : Odd (q ^ 2) := (Nat.odd_iff.mpr hq).pow
    obtain ⟨j, hj⟩ := hodd
    exact ⟨j + 1, by omega⟩
  have hm5 : 5 ≤ m := by omega
  have ha0 : 0 < a := by omega
  have hm0 : 0 < m := by omega
  have hq2 : q ^ 2 - 1 = a := by omega
  have hq4 : q ^ 4 - 1 = a * (a + 2) := by
    have : q ^ 4 = (a + 1) ^ 2 := by rw [← ha]; ring
    rw [this]
    exact Nat.sub_eq_of_eq_add (by ring)
  have hq44 : (q ^ 2) ^ 2 - 1 = a * (a + 2) := by
    rw [← hq4]
    congr 1
    ring
  have hq6 : q ^ 6 = (a + 1) ^ 3 := by rw [← ha]; ring
  have hM : n = (a + 1) * a * m := by
    rw [hn, hq44, ha, hm]
    have : (a + 1) * (a * (2 * m)) = 2 * ((a + 1) * a * m) := by ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hu : (q + 1) ∣ q ^ 3 + 1 := by
    obtain ⟨k, hk⟩ : ∃ k, q = 2 * k + 1 := ⟨q / 2, by omega⟩
    exact ⟨4 * k ^ 2 + 2 * k + 1, by rw [hk]; ring⟩
  have hg : Nat.gcd 4 (q + 1) ∣ q ^ 3 + 1 := (Nat.gcd_dvd_right 4 (q + 1)).trans hu
  have hP : Nat.gcd 4 (q + 1) ∣
      q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right hg _) _) _
  have hD' := hD.trans (Nat.div_dvd_of_dvd hP)
  rw [hq6, hq2, hq4, hM] at hD'
  obtain ⟨r, hr⟩ := hD'
  have hpos : 0 < 2 * (a + 1) ^ 2 * a ^ 2 * m := by positivity
  have key : (2 * (a + 1) ^ 2 * a ^ 2 * m) * ((a + 1) * (q ^ 3 + 1)) =
      (2 * (a + 1) ^ 2 * a ^ 2 * m) * (m * r) := by
    calc (2 * (a + 1) ^ 2 * a ^ 2 * m) * ((a + 1) * (q ^ 3 + 1))
        = (a + 1) ^ 3 * (a * ((q ^ 3 + 1) * (a * (a + 2)))) := by rw [hm]; ring
      _ = ((a + 1) * a * m * (2 * ((a + 1) * a * m))) * r := hr
      _ = (2 * (a + 1) ^ 2 * a ^ 2 * m) * (m * r) := by ring
  have hmu : m ∣ (a + 1) * (q ^ 3 + 1) := ⟨r, Nat.eq_of_mul_eq_mul_left hpos key⟩
  have hcop : Nat.Coprime m (a + 1) := by
    have h1 : Nat.Coprime (a + 2) (a + 1) := by
      have : a + 2 = (a + 1) + 1 := rfl
      rw [this]
      simp
    exact h1.coprime_dvd_left ⟨2, by omega⟩
  have hmu' : m ∣ q ^ 3 + 1 := by
    rw [mul_comm] at hmu
    exact hcop.dvd_of_dvd_mul_right hmu
  have h2m : q ^ 2 + 1 = 2 * m := by omega
  have hm1 : m ∣ q ^ 3 + q := ⟨2 * q, by
    calc q ^ 3 + q = q * (q ^ 2 + 1) := by ring
      _ = q * (2 * m) := by rw [h2m]
      _ = m * (2 * q) := by ring⟩
  have hdiv : m ∣ q ^ 3 + q - (q ^ 3 + 1) := Nat.dvd_sub hm1 hmu'
  have hsub : q ^ 3 + q - (q ^ 3 + 1) = q - 1 := by omega
  rw [hsub] at hdiv
  have hle := Nat.le_of_dvd (by omega) hdiv
  omega

theorem not_dvd_card_u4 (q : ℕ) (hq : q % 2 = 1) (h3 : 3 ≤ q) {n : ℕ}
    (hn : n = q ^ 2 * ((q ^ 2) ^ 2 - 1) / 2) : ¬ (n * (2 * n)) ∣ CFSG.Open.ordTwistedA 3 q := by
  intro hD
  rw [CFSG.ClassicalInvolution.RouteD.TWR.ordTwistedA_three_eq q (by omega)] at hD
  exact not_dvd_core q hq h3 hn hD

end KG531U4Arith

end CFSG.GH74.Generic.BProg.B3
