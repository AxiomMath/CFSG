module

public import CFSG.CGT.Stroth77.L4Sylow.SylowSU
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitInputs

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow

theorem litPSLU4S_of_lieModel_psl4_l4Sylow {G : Type} [Group G] [Finite G]
    {p f n : ℕ} (hp : p.Prime) (hf : 0 < f) (hq4 : p ^ f % 4 = 1)
    (hL : CFSG.Blueprint.LieModel G .PSL 4 p f) (hn : 3 ≤ n)
    (P : Sylow 2 G) (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) :
    CFSG.OddStandard.HigherRank.YamadaG23.LitPSLU4S G := by
  set q := p ^ f with hq
  have hq2 : 2 ≤ q := by
    calc 2 ≤ 2 ^ f := Nat.le_self_pow hf.ne' 2
      _ ≤ p ^ f := Nat.pow_le_pow_left hp.two_le f
  have hqpos : 0 < q - 1 := by omega
  let m := (q - 1).factorization 2
  have hm2 : 2 ≤ m := by
    have h4 : 4 ∣ q - 1 := by
      have : q % 4 = 1 := by simpa [hq] using hq4
      omega
    have h2dvd : 2 ^ 2 ∣ q - 1 := by simpa using h4
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hqpos.ne').1 h2dvd
  obtain ⟨eM⟩ := nonempty_mulEquiv_l4Model_of_lieModel (p := p) (f := f)
    (by simpa [hq] using hq4) hL P
  have hcard : 2 ^ (3 * n + 1) = 2 ^ (3 * m + 1) := by
    have h1 : Nat.card ↥(P : Subgroup G) = 2 ^ (3 * n + 1) := by
      rw [Nat.card_congr (Classical.choice hP).toEquiv, card_L4Model (by omega)]
    have h2 : Nat.card ↥(P : Subgroup G) = 2 ^ (3 * m + 1) := by
      rw [Nat.card_congr eM.toEquiv, card_L4Model (by omega)]
    rw [h1] at h2
    exact h2
  have hexp : 3 * n + 1 = 3 * m + 1 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2) hcard
  have hmn : m = n := by omega
  have hdvd : 2 ^ n ∣ q - 1 := by
    have hle : n ≤ (q - 1).factorization 2 := by omega
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hqpos.ne').2 hle
  have h8 : 8 ∣ q - 1 := by
    have h3 : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    simpa using h3.trans hdvd
  have hq8 : q % 8 = 1 := by
    obtain ⟨k, hk⟩ := h8
    have hqeq : q = 1 + 8 * k := by omega
    rw [hqeq, Nat.add_mul_mod_self_left]
  exact Or.inl ⟨p, f, hp, hf, by simpa [hq] using hq8, hL⟩

theorem litPSLU4S_of_lieModel_psu4_l4Sylow {G : Type} [Group G] [Finite G]
    {p f n : ℕ} (hp : p.Prime) (hf : 0 < f) (hq4 : p ^ f % 4 = 3)
    (hL : CFSG.Blueprint.LieModel G .PSU 4 p f) (hn : 3 ≤ n)
    (P : Sylow 2 G) (hP : Nonempty (↥(P : Subgroup G) ≃* L4Model n)) :
    CFSG.OddStandard.HigherRank.YamadaG23.LitPSLU4S G := by
  set q := p ^ f with hq
  have hq2 : 2 ≤ q := by
    calc 2 ≤ 2 ^ f := Nat.le_self_pow hf.ne' 2
      _ ≤ p ^ f := Nat.pow_le_pow_left hp.two_le f
  let m := (q + 1).factorization 2
  have hm2 : 2 ≤ m := by
    have h4 : 4 ∣ q + 1 := by
      have : q % 4 = 3 := by simpa [hq] using hq4
      omega
    have h2dvd : 2 ^ 2 ∣ q + 1 := by simpa using h4
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)).1 h2dvd
  obtain ⟨eM⟩ := nonempty_mulEquiv_l4Model_of_lieModel_psu (p := p) (f := f)
    (by simpa [hq] using hq4) hL P
  have hcard : 2 ^ (3 * n + 1) = 2 ^ (3 * m + 1) := by
    have h1 : Nat.card ↥(P : Subgroup G) = 2 ^ (3 * n + 1) := by
      rw [Nat.card_congr (Classical.choice hP).toEquiv, card_L4Model (by omega)]
    have h2 : Nat.card ↥(P : Subgroup G) = 2 ^ (3 * m + 1) := by
      rw [Nat.card_congr eM.toEquiv, card_L4Model (by omega)]
    rw [h1] at h2
    exact h2
  have hexp : 3 * n + 1 = 3 * m + 1 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2) hcard
  have hmn : m = n := by omega
  have hdvd : 2 ^ n ∣ q + 1 := by
    have hle : n ≤ (q + 1).factorization 2 := by omega
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by omega)).2 hle
  have h8 : 8 ∣ q + 1 := by
    have h3 : 2 ^ 3 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    simpa using h3.trans hdvd
  have hq8 : q % 8 = 7 := by
    obtain ⟨k, hk⟩ := h8
    have hk1 : 1 ≤ k := by omega
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have hqeq : q = 7 + 8 * k' := by omega
    rw [hqeq, Nat.add_mul_mod_self_left]
  exact Or.inr ⟨p, f, hp, hf, by simpa [hq] using hq8, hL⟩

end CFSG.LocalAnalysis.Mason73
