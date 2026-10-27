module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvArith
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvEngFive
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U4SvNine

public section

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Five

variable {p₀ f₀ : ℕ} {K : Type} [Field K]

theorem u4_five_three_false (h : UnitaryFieldData p₀ f₀ K) (hq : p₀ ^ f₀ = 5)
    {X₀ : Subgroup ↥(hypSU h 2 0)} (hX : IsPGroup 3 ↥X₀) (hcard : Nat.card ↥X₀ = 81)
    (hQ : Nat.card (↥X₀ ⧸ frattini ↥X₀) = 81) : False := by
  have := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 ↥X₀) := ⟨hX⟩
  have hΦ : Nat.card (frattini ↥X₀) = 1 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini ↥X₀)
    rw [hcard, hQ] at h1
    omega
  have hbot : frattini ↥X₀ = ⊥ := Subgroup.eq_bot_of_card_eq _ hΦ
  have hexp : ∀ x ∈ X₀, x ^ 3 = 1 := by
    intro x hx
    have h1 := CFSG.pth_power_mem_frattini_of_isPGroup (p := 3) (R := ↥X₀) ⟨x, hx⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  obtain ⟨g, hg⟩ := exists_orderOf_nine_hypSU h hq
  have hG : (Nat.card ↥(hypSU h 2 0)).factorization 3 = 4 := by
    rw [Nat.factorization_def _ Nat.prime_three]
    exact padicValNat_three_card_hypSU_five h hq
  obtain ⟨x, hx, hx3⟩ := exists_pow_three_ne_one_of_card_81 hG hg hcard
  exact hx3 (hexp x hx)

end Five

section Engines

variable {p₀ f₀ : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p₀ f₀ K) {p : ℕ} [Fact p.Prime]

theorem padicValNat_card_le_hypSU (X₀ : Subgroup ↥(hypSU h 2 0)) :
    padicValNat p (Nat.card ↥X₀) ≤ padicValNat p (Nat.card ↥(hypSU h 2 0)) := by
  have := h.finite
  exact (padicValNat_dvd_iff_le Nat.card_pos.ne').1
    (pow_padicValNat_dvd.trans (Subgroup.card_subgroup_dvd_card X₀))

theorem u4_sl2_engineK (hodd : Odd (p₀ ^ f₀)) (h3 : 3 ≤ p₀ ^ f₀) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ p₀ ^ f₀) {X₀ : Subgroup ↥(hypSU h 2 0)} (hX : IsPGroup p ↥X₀)
    (ι : SL2 K →* ↥(hypSU h 2 0)) (hnorm : ∀ g, ι g ∈ normalizer (X₀ : Set ↥(hypSU h 2 0))) :
    ∀ g, ∀ x ∈ X₀, ι g * x = x * ι g := by
  have := h.finite
  have hK : Nat.card K = (p₀ ^ f₀) ^ 2 := by rw [h.card, pow_mul']
  have hodd' : Odd (Nat.card K) := by rw [hK]; exact hodd.pow
  have h5 : 5 ≤ Nat.card K := by rw [hK]; nlinarith
  have hpK : ¬ p ∣ Nat.card K := fun hd => hpq ((Fact.out : p.Prime).dvd_of_dvd_pow (hK ▸ hd))
  rcases sl2_centralizes_or_large hp2 hodd' h5 hpK ι hX hnorm with hc | hlarge
  · exact hc
  · exfalso
    have h1 := padicValNat_card_le_hypSU h (p := p) X₀
    have h2 := padicValNat_card_hypSU_lt_sq (p := p) h hodd h3 hp2 hpq
    rw [hK] at hlarge
    omega

theorem u4_sl2_engineQ (hodd : Odd (p₀ ^ f₀)) (h5 : 5 ≤ p₀ ^ f₀) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ p₀ ^ f₀) {X₀ : Subgroup ↥(hypSU h 2 0)} (hX : IsPGroup p ↥X₀)
    (ι : SL2 ↥h.fixedField →* ↥(hypSU h 2 0))
    (hnorm : ∀ g, ι g ∈ normalizer (X₀ : Set ↥(hypSU h 2 0))) :
    ∀ g, ∀ x ∈ X₀, ι g * x = x * ι g := by
  have := h.finite
  have hF : Nat.card ↥h.fixedField = p₀ ^ f₀ := h.card_fixedField
  have hoddF : Odd (Nat.card ↥h.fixedField) := hF ▸ hodd
  have h5F : 5 ≤ Nat.card ↥h.fixedField := hF ▸ h5
  have hpF : ¬ p ∣ Nat.card ↥h.fixedField := hF ▸ hpq
  by_cases hexc : p₀ ^ f₀ = 5 ∧ p = 3
  · obtain ⟨hq5, rfl⟩ := hexc
    have hFcard : Nat.card ↥h.fixedField = 5 := hF.trans hq5
    by_cases hQ : Nat.card (↥X₀ ⧸ frattini ↥X₀) ≤ 27
    · exact sl2_centralizes_five_three_d3 hFcard ι hX hnorm hQ
    · exfalso
      push Not at hQ
      have hv : padicValNat 3 (Nat.card ↥(hypSU h 2 0)) = 4 :=
        padicValNat_three_card_hypSU_five h hq5
      obtain ⟨k, hk⟩ := hX.exists_card_eq
      have hk4 : k ≤ 4 := by
        have hdvd : 3 ^ k ∣ Nat.card ↥(hypSU h 2 0) := hk ▸ Subgroup.card_subgroup_dvd_card X₀
        have := (padicValNat_dvd_iff_le Nat.card_pos.ne').1 hdvd
        omega
      obtain ⟨j, hj⟩ := (hX.to_quotient (frattini ↥X₀)).exists_card_eq
      have hjk : j ≤ k := by
        have hdvd : 3 ^ j ∣ 3 ^ k := by
          rw [← hj, ← hk]
          exact Subgroup.card_quotient_dvd_card _
        exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
      have hj3 : 3 < j := by
        have : 3 ^ 3 < 3 ^ j := by rw [← hj]; exact hQ
        exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
      have hj4 : j = 4 := by omega
      have hk4' : k = 4 := by omega
      exact u4_five_three_false h hq5 hX (by rw [hk, hk4']; norm_num)
        (by rw [hj, hj4]; norm_num)
  · rcases sl2_centralizes_or_large hp2 hoddF h5F hpF ι hX hnorm with hc | hlarge
    · exact hc
    · exfalso
      have h1 := padicValNat_card_le_hypSU h (p := p) X₀
      have h2 := padicValNat_card_hypSU_lt h hodd h5 hp2 hpq hexc
      rw [hF] at hlarge
      omega

end Engines

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
