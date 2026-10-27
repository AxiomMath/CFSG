module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.AltFixedCard

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion.KDM22Proof

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private lemma not_dvd_two_pow (e : ℕ) : ¬(11 ∣ 2 ^ e) := fun h =>
  absurd (Nat.prime_eleven.dvd_of_dvd_pow h) (by norm_num)

private lemma dvd_or_dvd_of_dvd_two_pow_mul_mul {e a b : ℕ}
    (h : 11 ∣ 2 ^ e * a * b) : 11 ∣ a ∨ 11 ∣ b := by
  rcases Nat.prime_eleven.dvd_mul.1 h with h | h
  · rcases Nat.prime_eleven.dvd_mul.1 h with h | h
    · exact absurd h (not_dvd_two_pow e)
    · exact Or.inl h
  · exact Or.inr h

private lemma eleven_factorial_le_of_dvd {r n : ℕ}
    (h : 11 ∣ 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial) :
    Nat.factorial 11 ≤ 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial := by
  have hpow : (1 : ℕ) ≤ 2 ^ (r - 1) := Nat.one_le_pow _ _ (by norm_num)
  have hfac : (1 : ℕ) ≤ r.factorial := Nat.one_le_of_lt (Nat.factorial_pos r)
  have hfac' : (1 : ℕ) ≤ (n - 2 * r).factorial :=
    Nat.one_le_of_lt (Nat.factorial_pos _)
  rcases dvd_or_dvd_of_dvd_two_pow_mul_mul h with h | h
  · have hr : 11 ≤ r := Nat.prime_eleven.dvd_factorial.mp h
    have h11 : Nat.factorial 11 ≤ r.factorial := Nat.factorial_le hr
    calc
      Nat.factorial 11 = (1 * Nat.factorial 11) * 1 := by ring
      _ ≤ 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial :=
        Nat.mul_le_mul (Nat.mul_le_mul hpow h11) hfac'
  · have hn : 11 ≤ n - 2 * r := Nat.prime_eleven.dvd_factorial.mp h
    have h11 : Nat.factorial 11 ≤ (n - 2 * r).factorial := Nat.factorial_le hn
    calc
      Nat.factorial 11 = (1 * 1) * Nat.factorial 11 := by ring
      _ ≤ 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial :=
        Nat.mul_le_mul (Nat.mul_le_mul hpow hfac) h11

theorem false_of_alt {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 5 ≤ n)
    (θ : S ≃* alternatingGroup (Fin n)) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hdvd : 443520 ∣ Nat.card (fixedSubgroup σ))
    (hle : Nat.card (fixedSubgroup σ) ≤ 4 * 443520) : False := by
  have h11dvd : (11 : ℕ) ∣ 443520 := by norm_num
  have h11 : 11 ∣ Nat.card (fixedSubgroup σ) := h11dvd.trans hdvd
  rcases Nat.lt_or_ge n 7 with h7 | h7
  · have hge : 443520 ≤ Nat.card (fixedSubgroup σ) := Nat.le_of_dvd Nat.card_pos hdvd
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have hS : Nat.card S = n.factorial / 2 := by
      rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    have hleS : Nat.card (fixedSubgroup σ) ≤ n.factorial / 2 := by
      simpa [hS] using Subgroup.card_le_card_group (fixedSubgroup σ)
    have hfac : n.factorial ≤ 720 := by
      have h := Nat.factorial_le (show n ≤ 6 by omega)
      norm_num [Nat.factorial] at h
      exact h
    have hdiv : n.factorial / 2 ≤ 360 := by
      calc
        n.factorial / 2 ≤ 720 / 2 := Nat.div_le_div_right hfac
        _ = 360 := by norm_num
    omega
  · obtain ⟨r, -, -, hcard⟩ :=
      CFSG.ComponentClassification.CatFC.card_fixedSubgroup_alt h7 θ hσ
    have h11' : 11 ∣ 2 ^ (r - 1) * r.factorial * (n - 2 * r).factorial := by
      rwa [hcard] at h11
    have hNge : Nat.factorial 11 ≤ Nat.card (fixedSubgroup σ) := by
      rw [hcard]
      exact eleven_factorial_le_of_dvd h11'
    have hnum : 4 * 443520 < Nat.factorial 11 := by decide
    omega

end CFSG.EvenSporadicStandard.Co2Std.Exclusion.KDM22Proof
