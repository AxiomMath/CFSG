module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBasic

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

theorem linTwo_not_dvd_unitaryOrder {p : ℕ} (hp3 : 3 ≤ p) (hodd : Odd p) :
    ¬ p ^ 2 * (((p ^ 2) ^ 2 - 1) / 2) ∣ p ^ 3 * (p ^ 3 + 1) * (p ^ 2 - 1) := by
  obtain ⟨k, rfl⟩ := hodd
  have hk : 1 ≤ k := by omega
  intro h
  have e1 : (2 * k + 1) ^ 2 - 1 = 4 * k * (k + 1) := by
    have : (2 * k + 1) ^ 2 = 4 * k * (k + 1) + 1 := by ring
    omega
  have e2 : (((2 * k + 1) ^ 2) ^ 2 - 1) / 2 = 4 * k * (k + 1) * (2 * k ^ 2 + 2 * k + 1) := by
    have : ((2 * k + 1) ^ 2) ^ 2 = 2 * (4 * k * (k + 1) * (2 * k ^ 2 + 2 * k + 1)) + 1 := by
      ring
    omega
  rw [e1, e2] at h
  set r := 2 * k ^ 2 + 2 * k + 1 with hrdef
  have hc : 0 < (2 * k + 1) ^ 2 * (4 * k * (k + 1)) := by positivity
  have h' : (2 * k + 1) ^ 2 * (4 * k * (k + 1)) * r ∣
      (2 * k + 1) ^ 2 * (4 * k * (k + 1)) * ((2 * k + 1) * ((2 * k + 1) ^ 3 + 1)) := by
    convert h using 1 <;> ring
  have h2 : r ∣ (2 * k + 1) * ((2 * k + 1) ^ 3 + 1) := Nat.dvd_of_mul_dvd_mul_left hc h'
  have hcop1 : Nat.Coprime r (2 * k + 1) := by
    rw [← Nat.isCoprime_iff_coprime]
    exact ⟨2, -(2 * k + 1), by push_cast; rw [hrdef]; push_cast; ring⟩
  have hcop2 : Nat.Coprime r ((2 * k + 1) ^ 3 + 1) := by
    rw [← Nat.isCoprime_iff_coprime]
    exact ⟨1 - (2 * k + 2) * (2 * k + 1), k + 1, by push_cast; rw [hrdef]; push_cast; ring⟩
  have h3 : r ∣ (2 * k + 1) ^ 3 + 1 := hcop1.dvd_of_dvd_mul_left h2
  have h4 : r = 1 := Nat.Coprime.eq_one_of_dvd hcop2 h3
  have : 5 ≤ r := by rw [hrdef]; nlinarith
  omega

theorem lt_factorial_two_mul {p : ℕ} (hp : p = 5 ∨ 7 ≤ p) :
    p ^ 3 * (p ^ 3 + 1) * (p ^ 2 - 1) < (2 * p).factorial / 2 := by
  have hlt : p ^ 3 * (p ^ 3 + 1) * (p ^ 2 - 1) < p ^ 8 := by
    have h5 : 5 ≤ p := by omega
    have h2 : (p ^ 3 + 1) * (p ^ 2 - 1) < p ^ 3 * p ^ 2 := by
      have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ (by omega)
      obtain ⟨m, hm⟩ : ∃ m, p ^ 2 = m + 1 := ⟨p ^ 2 - 1, by omega⟩
      rw [hm]
      simp only [Nat.add_sub_cancel]
      have h3 : p ^ 3 = p * (m + 1) := by rw [← hm]; ring
      have hp1 : 1 < p ^ 2 := by nlinarith
      nlinarith
    calc p ^ 3 * (p ^ 3 + 1) * (p ^ 2 - 1) = p ^ 3 * ((p ^ 3 + 1) * (p ^ 2 - 1)) := by ring
      _ < p ^ 3 * (p ^ 3 * p ^ 2) := Nat.mul_lt_mul_of_pos_left h2 (by positivity)
      _ = p ^ 8 := by ring
  rcases hp with rfl | h7
  · norm_num [Nat.factorial]
  · have h := @Nat.factorial_mul_pow_le_factorial (2 * p - 8) 8
    have e : 2 * p - 8 + 8 = 2 * p := by omega
    rw [e] at h
    have hf : 2 ≤ (2 * p - 8).factorial :=
      calc 2 = (2 : ℕ).factorial := by norm_num
        _ ≤ (2 * p - 8).factorial := Nat.factorial_le (by omega)
    have hpow : p ^ 8 ≤ (2 * p - 8 + 1) ^ 8 := Nat.pow_le_pow_left (by omega) 8
    have h2 : 2 * p ^ 8 ≤ (2 * p).factorial :=
      calc 2 * p ^ 8 ≤ (2 * p - 8).factorial * (2 * p - 8 + 1) ^ 8 := Nat.mul_le_mul hf hpow
        _ ≤ (2 * p).factorial := h
    omega

theorem card_eq_sq_of_noncyclic {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (T : Subgroup G)
    (hT : ¬ IsCyclic T) (hdvd : Nat.card T ∣ p ^ 2) :
    Nat.card T = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha, hTa⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  interval_cases a
  · exfalso
    apply hT
    have : Nat.card T = 1 := by simpa using hTa
    have : Subsingleton T := (Nat.card_eq_one_iff_unique.1 this).1
    exact isCyclic_of_subsingleton
  · exfalso
    apply hT
    exact isCyclic_of_prime_card (by simpa using hTa)
  · exact hTa

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
