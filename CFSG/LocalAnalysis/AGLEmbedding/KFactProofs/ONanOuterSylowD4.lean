module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOuterSylowStep
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs

public section

namespace CFSG.AGLEmbedding.OuterSylow

open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator)

section Arith

theorem numerator_trialityD4_mul (q : ℕ) (hq : 1 ≤ q) :
    lieOrderNumerator .trialityD4 0 q * (q ^ 2 + 1) =
      q ^ 12 * (q ^ 6 - 1) * (q ^ 6 - 1) * (q ^ 6 + 1) := by
  simp only [lieOrderNumerator]
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
  zify [h2, h6]
  ring

theorem numerator_trialityD4_eq_mul_G2 (q : ℕ) :
    lieOrderNumerator .trialityD4 0 q =
      lieOrderNumerator .G2 0 q * (q ^ 6 * (q ^ 8 + q ^ 4 + 1)) := by
  simp only [lieOrderNumerator]
  ring

theorem sq_mod_three (q : ℕ) (h : ¬ 3 ∣ q) : q ^ 2 % 3 = 1 := by
  have : q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases this with h | h <;> simp [pow_two, Nat.mul_mod, h]

theorem three_dvd_sixth_mul (q : ℕ) : 3 ∣ q ^ 6 * (q ^ 8 + q ^ 4 + 1) := by
  by_cases h3 : 3 ∣ q
  · exact Dvd.dvd.mul_right (dvd_pow h3 (by norm_num)) _
  · refine Dvd.dvd.mul_left ?_ _
    have h2 := sq_mod_three q h3
    have h4 : q ^ 4 % 3 = 1 := by
      rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, Nat.pow_mod, h2]
    have h8 : q ^ 8 % 3 = 1 := by
      rw [show q ^ 8 = (q ^ 4) ^ 2 by ring, Nat.pow_mod, h4]
    omega

theorem not_three_dvd_sq_add_one (q : ℕ) : ¬ 3 ∣ q ^ 2 + 1 := by
  intro h
  by_cases h3 : 3 ∣ q
  · have : 3 ∣ q ^ 2 := dvd_pow h3 (by norm_num)
    omega
  · have := sq_mod_three q h3
    omega

theorem mul_sub_one_eq (q : ℕ) (hq : 1 ≤ q) :
    (q ^ 8 + q ^ 4 + 1) * (q ^ 4 - 1) = (q ^ 6 - 1) * (q ^ 6 + 1) := by
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq
  zify [h4, h6]
  ring

theorem eight_four_one_eq (q : ℕ) (hq : 1 ≤ q) :
    q ^ 8 + q ^ 4 + 1 = (q ^ 4 - 1) * (q ^ 4 + 2) + 3 := by
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  zify [h4]
  ring

theorem four_sub_one_eq (q : ℕ) (hq : 1 ≤ q) : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  zify [h2, h4]
  ring

theorem sq_sub_one_dvd_sixth (q : ℕ) : q ^ 2 - 1 ∣ q ^ 6 - 1 := by
  have := Nat.sub_dvd_pow_sub_pow (q ^ 2) 1 3
  simpa [← pow_mul] using this

end Arith

section Valuation

variable {p : ℕ} [hp : Fact p.Prime]

theorem dvd_eight_four_one_of_dvd_pow {q : ℕ} (h : p ∣ (q ^ p) ^ 8 + (q ^ p) ^ 4 + 1) :
    p ∣ q ^ 8 + q ^ 4 + 1 := by
  have h1 : (((q ^ p) ^ 8 + (q ^ p) ^ 4 + 1 : ℕ) : ZMod p) =
      ((q ^ 8 + q ^ 4 + 1 : ℕ) : ZMod p) := by
    push_cast
    rw [ZMod.pow_card]
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  rwa [h1] at h

theorem dvd_factor_of_dvd_numerator_trialityD4 (hodd : Odd p) {q : ℕ} (hq : 2 ≤ q)
    (hpq : ¬ p ∣ q) (h : p ∣ lieOrderNumerator .trialityD4 0 (q ^ p)) :
    p ∣ q ^ 6 - 1 ∨ p ∣ q ^ 2 - 1 ∨ p ∣ q ^ 8 + q ^ 4 + 1 := by
  simp only [lieOrderNumerator] at h
  rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp.out).1 h with h | h
      · exact absurd (hp.out.dvd_of_dvd_pow (hp.out.dvd_of_dvd_pow h)) hpq
      · exact Or.inr (Or.inr (dvd_eight_four_one_of_dvd_pow h))
    · exact Or.inl ((Stp.sub_pow' hodd (by omega) 6).2.2.2.1 h)
  · exact Or.inr (Or.inl ((Stp.sub_pow' hodd (by omega) 2).2.2.2.1 h))

theorem numerator_trialityD4_factorization_lt (hp2 : p ≠ 2) {q : ℕ} (hq : 2 ≤ q)
    (h : p ∣ lieOrderNumerator .trialityD4 0 (q ^ p)) :
    (lieOrderNumerator .trialityD4 0 q).factorization p <
      (lieOrderNumerator .trialityD4 0 (q ^ p)).factorization p := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    rcases hodd with ⟨r, hr⟩
    omega
  have hq1 : 1 ≤ q := by omega
  have hqp : 1 ≤ q ^ p := Nat.one_le_pow _ _ hq1
  rw [Nat.factorization_def _ hp.out, Nat.factorization_def _ hp.out]
  have hQ := Stp.pow_q (p := p) hp3 hq1 (N := 12) (by norm_num)
  have hB := Stp.sub_pow' (p := p) hodd hq 6
  have hF := Stp.add_pow' (p := p) hodd hq1 6
  have hE := Stp.add_pow' (p := p) hodd hq1 2
  have hR := ((hQ.mul hB).mul hB).mul hF
  have iden := numerator_trialityD4_mul q hq1
  have iden' := numerator_trialityD4_mul (q ^ p) hqp
  have ha0 : lieOrderNumerator .trialityD4 0 q ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at iden
    exact hR.1 iden.symm
  have hb0 : lieOrderNumerator .trialityD4 0 (q ^ p) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at iden'
    exact hR.2.1 iden'.symm
  have h1 := hR.2.2.1
  rw [← iden', padicValNat.mul hb0 (by omega), ← iden, padicValNat.mul ha0 (by omega)] at h1
  have h2 := hE.2.2.1
  by_cases hpq : p ∣ q
  · have hv := one_le_padicValNat_of_dvd (by omega : q ≠ 0) hpq
    have hk : 2 ≤ 12 * (p - 1) * padicValNat p q := by
      calc 2 ≤ 12 * 2 * 1 := by norm_num
        _ ≤ 12 * (p - 1) * padicValNat p q := by
          gcongr
          omega
    split_ifs at h1 h2 <;> omega
  · have hkQ : 12 * (p - 1) * padicValNat p q = 0 := by
      rw [padicValNat.eq_zero_of_not_dvd hpq]
      simp
    have hcases := dvd_factor_of_dvd_numerator_trialityD4 hodd hq hpq h
    by_cases hBd : p ∣ q ^ 6 - 1
    · simp only [hBd, ↓reduceIte] at h1
      split_ifs at h1 h2 <;> omega
    · by_cases hFd : p ∣ q ^ 6 + 1
      · by_cases hEd : p ∣ q ^ 2 + 1
        · exfalso
          rcases hcases with h6 | hA | hC
          · exact hBd h6
          · have h2' := Nat.dvd_sub hEd hA
            rw [show q ^ 2 + 1 - (q ^ 2 - 1) = 2 by
              have := Nat.one_le_pow 2 q hq1
              omega] at h2'
            exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h2')
          · have hdvd4 : p ∣ q ^ 4 - 1 := by
              rw [four_sub_one_eq q hq1]
              exact Dvd.dvd.mul_left hEd _
            rw [eight_four_one_eq q hq1] at hC
            have h3 : p ∣ 3 := (Nat.dvd_add_right (Dvd.dvd.mul_right hdvd4 _)).1 hC
            have hp3' : p = 3 := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1 h3
            subst hp3'
            exact not_three_dvd_sq_add_one q hEd
        · simp only [hBd, hFd, hEd, ↓reduceIte] at h1 h2
          omega
      · exfalso
        rcases hcases with h6 | hA | hC
        · exact hBd h6
        · exact hBd (hA.trans (sq_sub_one_dvd_sixth q))
        · have : p ∣ (q ^ 6 - 1) * (q ^ 6 + 1) := by
            rw [← mul_sub_one_eq q hq1]
            exact Dvd.dvd.mul_right hC _
          rcases (Nat.Prime.dvd_mul hp.out).1 this with h6 | h6
          · exact hBd h6
          · exact hFd h6

end Valuation

theorem factorization_G2_lt_trialityD4 {q : ℕ} (hq : 2 ≤ q) :
    (lieOrderNumerator .G2 0 q).factorization 3 <
      (lieOrderNumerator .trialityD4 0 q).factorization 3 := by
  have hq0 : q ≠ 0 := by omega
  have hG : lieOrderNumerator .G2 0 q ≠ 0 := by
    have h6 : 1 < q ^ 6 := Nat.one_lt_pow (by norm_num) (by omega)
    have h2 : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    simp only [lieOrderNumerator]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hq0) (by omega)) (by omega)
  have hX : q ^ 6 * (q ^ 8 + q ^ 4 + 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hq0) (by omega)
  rw [numerator_trialityD4_eq_mul_G2, Nat.factorization_mul hG hX]
  have := Nat.Prime.factorization_pos_of_dvd Nat.prime_three hX (three_dvd_sixth_mul q)
  simp only [Finsupp.add_apply]
  omega

end CFSG.AGLEmbedding.OuterSylow
