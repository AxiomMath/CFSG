module

public import CFSG.CGT.T75E.RootCommon
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders

public noncomputable section

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki CFSG.Open

theorem card_psu3Model_mul_gcd {f : ℕ} (hf : 1 ≤ f) :
    Nat.card (PSU3Model f) * Nat.gcd 3 (2 ^ f + 1) =
      (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) :=
  CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psu3_mul_gcd hf

theorem le_of_two_pow_dvd_mul_odd {a b r : ℕ} (hr : Odd r) (h : 2 ^ a ∣ 2 ^ b * r) : a ≤ b := by
  by_contra hab
  have hab' : b < a := not_le.1 hab
  have h1 : 2 ^ (b + 1) ∣ 2 ^ a := pow_dvd_pow 2 hab'
  have h2 : 2 ^ (b + 1) ∣ 2 ^ b * r := h1.trans h
  rw [pow_succ] at h2
  have h3 : 2 ∣ r := Nat.dvd_of_mul_dvd_mul_left (by positivity) h2
  exact absurd h3 (by simpa [Nat.odd_iff] using hr)

theorem exists_odd_card_psu3Model {f : ℕ} (hf : 1 ≤ f) :
    ∃ r : ℕ, Odd r ∧ Nat.card (PSU3Model f) = 2 ^ (3 * f) * r := by
  have hmul := card_psu3Model_mul_gcd hf
  set g := Nat.gcd 3 (2 ^ f + 1) with hg
  set N := ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) with hNdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hgodd : Odd g := Odd.of_dvd_nat (by decide : Odd 3) (Nat.gcd_dvd_left _ _)
  have hx : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by omega⟩
  have h1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ Nat.one_le_two_pow
  have hN : Odd N := by
    refine Odd.mul ?_ ?_
    · obtain ⟨k, hk⟩ := (Nat.even_pow.2 ⟨hx, by norm_num⟩ : Even ((2 ^ f) ^ 2))
      exact ⟨k - 1, by omega⟩
    · exact (Nat.even_pow.2 ⟨hx, by norm_num⟩ : Even ((2 ^ f) ^ 3)).add_one
  have hpow : (2 ^ f) ^ 3 = 2 ^ (3 * f) := by rw [← pow_mul, mul_comm]
  have hcop : Nat.Coprime g ((2 ^ f) ^ 3) := by
    rw [hpow]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hgodd)
  have hgN : g ∣ N := by
    have : g ∣ (2 ^ f) ^ 3 * N := by
      rw [← hmul]
      exact Dvd.intro_left _ rfl
    exact hcop.dvd_of_dvd_mul_left this
  obtain ⟨r, hr⟩ := hgN
  refine ⟨r, Odd.of_dvd_nat hN (Dvd.intro_left g hr.symm), ?_⟩
  have : Nat.card (PSU3Model f) * g = (2 ^ f) ^ 3 * r * g := by
    rw [hmul, hr]
    ring
  rw [← hpow]
  exact Nat.eq_of_mul_eq_mul_right hg0 this

theorem three_dvd_card_psu3Model {f : ℕ} (hf : 1 ≤ f) : 3 ∣ Nat.card (PSU3Model f) := by
  have hmul := card_psu3Model_mul_gcd hf
  have h4 : 3 ∣ (2 ^ f) ^ 2 - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow 4 1 f
    have e : (2 ^ f) ^ 2 = 4 ^ f := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [e]
    simpa using h
  by_cases h3 : 3 ∣ 2 ^ f + 1
  · have hg : Nat.gcd 3 (2 ^ f + 1) = 3 := Nat.gcd_eq_left h3
    rw [hg] at hmul
    have h9 : 3 ∣ ((2 ^ f) ^ 3 + 1) := by
      have h' := (by decide : Odd 3).nat_add_dvd_pow_add_pow (2 ^ f) 1
      simpa using h3.trans h'
    obtain ⟨u, hu⟩ := h4
    obtain ⟨v, hv⟩ := h9
    have h2 : Nat.card (PSU3Model f) * 3 = (3 * ((2 ^ f) ^ 3 * (u * v))) * 3 := by
      rw [hmul, hu, hv]
      ring
    have h3' := Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3) h2
    rw [h3']
    exact Dvd.intro _ rfl
  · have hg : Nat.gcd 3 (2 ^ f + 1) = 1 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    rw [hg, mul_one] at hmul
    rw [hmul]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h4 _) _

theorem card_psu3Model_gt {f : ℕ} (hf : 2 ≤ f) : 360 < Nat.card (PSU3Model f) := by
  have hmul := card_psu3Model_mul_gcd (f := f) (by omega)
  have hx : 4 ≤ 2 ^ f :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h3 : 4 ^ 3 ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left hx 3
  have h2' : 4 ^ 2 ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left hx 2
  have h2 : 15 ≤ (2 ^ f) ^ 2 - 1 := by omega
  have h3' : 65 ≤ (2 ^ f) ^ 3 + 1 := by omega
  have hbig : 62400 ≤ (2 ^ f) ^ 3 * (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1)) :=
    calc 62400 = 4 ^ 3 * (15 * 65) := by norm_num
      _ ≤ _ := Nat.mul_le_mul h3 (Nat.mul_le_mul h2 h3')
  have hg : Nat.gcd 3 (2 ^ f + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  by_contra hle
  have hle' : Nat.card (PSU3Model f) ≤ 360 := not_lt.1 hle
  have : Nat.card (PSU3Model f) * Nat.gcd 3 (2 ^ f + 1) ≤ 360 * 3 := Nat.mul_le_mul hle' hg
  omega

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem not_three_dvd_card_of_mulEquiv_sz {K : Type} [Group K]
    {a : ℕ} (e : K ≃* Sz a) : ¬ 3 ∣ Nat.card K := by
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hq2 : (2 ^ (2 * a + 1)) ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  rw [Nat.card_congr e.toEquiv, CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz a,
    Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.mul_mod ((2 ^ (2 * a + 1)) ^ 2), hq2,
    show ((2 ^ (2 * a + 1)) ^ 2 + 1) % 3 = 2 by omega,
    show (2 ^ (2 * a + 1) - 1) % 3 = 1 by omega]
  norm_num

theorem card_psu3_dvd_card {K : Type} [Group K] [Finite K] {Tb : Subgroup K} {c₁ c₂ : K} {f : ℕ}
    (ρ : ↥(Y3 Tb c₁ c₂) →* PSU3Model f) (hρ : Function.Surjective ρ) :
    Nat.card (PSU3Model f) ∣ Nat.card K :=
  (Subgroup.card_dvd_of_surjective hρ).trans (Subgroup.card_subgroup_dvd_card _)

end CFSG.CGT.T75E
