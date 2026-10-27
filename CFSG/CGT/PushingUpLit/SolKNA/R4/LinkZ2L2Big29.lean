module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big24
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big25
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big30

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W CFSG.GorensteinWalter
open CFSG.Blueprint

section L1Gamma

variable {F : Type} [Field F] [Finite F] {p f : ℕ}

theorem two_pow_dvd_and_not_dvd_of_mod {p f r : ℕ} (hr : 4 ≤ r)
    (h : p ^ f % 2 ^ (r + 1) = 2 ^ r + 1) :
    2 ^ r ∣ p ^ f - 1 ∧ ¬ 2 ^ (r + 1) ∣ p ^ f - 1 := by
  constructor
  · have hdvd : 2 ^ r ∣ 2 ^ (r + 1) := by
      rw [pow_succ]
      exact dvd_mul_right _ _
    have hmod : (2 ^ r + 1) % 2 ^ r = 1 := by
      have h1 : (1 : ℕ) < 2 ^ r := by
        have hle := Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) (show 1 ≤ r by omega)
        norm_num at hle
        omega
      calc (2 ^ r + 1) % 2 ^ r = (1 + 1 * 2 ^ r) % 2 ^ r := by ring_nf
        _ = 1 % 2 ^ r := Nat.add_mul_mod_self_right 1 1 (2 ^ r)
        _ = 1 := Nat.mod_eq_of_lt h1
    have hmodr : p ^ f % 2 ^ r = 1 := by
      have hthis := Nat.mod_mod_of_dvd (p ^ f) hdvd
      rw [h] at hthis
      rw [hmod] at hthis
      exact hthis.symm
    simpa [hmodr] using Nat.dvd_sub_mod (n := 2 ^ r) (p ^ f)
  · intro hd
    have h1lt : (1 : ℕ) < 2 ^ (r + 1) :=
      Nat.one_lt_pow (by omega : r + 1 ≠ 0) (by norm_num)
    have hm : 1 ≡ p ^ f [MOD 2 ^ (r + 1)] :=
      (Nat.modEq_iff_dvd' (by
        have := Nat.mod_le (p ^ f) (2 ^ (r + 1))
        rw [h] at this
        omega)).mpr hd
    have h1 : p ^ f % 2 ^ (r + 1) = 1 := by
      rw [← hm, Nat.mod_eq_of_lt h1lt]
    have hcontra : 2 ^ r + 1 = 1 := by rw [← h, h1]
    exact absurd hcontra (by have hp : 0 < 2 ^ r := pow_pos (by norm_num) r; omega)

theorem l1_gamma [Fact p.Prime] (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2) (hf : Even f) {r : ℕ}
    (hr : 4 ≤ r) (harith : p ^ f % 2 ^ (r + 1) = 2 ^ r + 1) {σ₀ : F ≃+* F} (hσ₀1 : σ₀ ≠ 1)
    (hσ₀2 : σ₀ * σ₀ = 1) (hq : ∀ x : F, σ₀ x = x ^ p ^ (f / 2))
    (N : Subgroup (PGammaL2 F)) [N.Normal]
    (hN1 : ∀ g : PGammaL2 F, g.right = 1 → g.left ∈ pslRange F → g ∈ N)
    (hN2 : ∃ y : Fˣ, ¬ IsSquare y ∧ (gD y σ₀ ∈ N ∨ gA y σ₀ ∈ N))
    {H S : Subgroup (PGammaL2 F)} (hH : IsPGroup 2 ↥H) (hHM : H ≤ monGrp F) (hSH : S ≤ H)
    (hS : IsSylow2In S N) {y : PGammaL2 F} (hy : y ∈ H) :
    ∃ s ∈ S, 2 ^ padicValNat 2 f < orderOf (y * s) := by
  have h4 : 4 ≤ p ^ f := by
    have hle : 2 ^ r + 1 ≤ p ^ f := by
      rw [← harith]
      exact Nat.mod_le _ _
    have h16 : 16 ≤ 2 ^ r := by
      have := Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) hr
      norm_num at this
      exact this
    omega
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp only [pow_zero] at h4
    omega
  have h2 : (2 : F) ≠ 0 := (field_facts (Fact.out : p.Prime) hp2 hF h4).2
  have hcard : Nat.card Fˣ = p ^ f - 1 := card_units_eq_of_card hF
  obtain ⟨hc1', hc2'⟩ := two_pow_dvd_and_not_dvd_of_mod hr harith
  have hc1 : 2 ^ r ∣ Nat.card Fˣ := by rw [hcard]; exact hc1'
  have hc2 : ¬ 2 ^ (r + 1) ∣ Nat.card Fˣ := by rwa [hcard]
  have h4dvd : 4 ∣ Nat.card Fˣ := by
    have h42 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h42, hcard]
    exact dvd_trans (pow_dvd_pow 2 (by omega : 2 ≤ r)) hc1'
  obtain ⟨e, s, ψ, he, hpv, hψo, hs, hodd, hsr, hσ₀'⟩ :=
    exists_frobenius_two_power hF hp2 hf hf0 hσ₀1 hq
  have harith' : s ^ 2 ^ e % 2 ^ (r + 1) = 2 ^ r + 1 := by rw [hsr]; exact harith
  obtain ⟨ξ, hξ⟩ := exists_unit_orderOf_eq (2 ^ r) hc1
  have hP : IsSylow2In (stdSylow ξ ψ) (monGrp F) :=
    isSylow2In_stdSylow hF hp2 h4 hξ hc1 hc2 (by rw [hpv]; exact hψo)
  have hN1sq : ∀ v : Fˣ, IsSquare v → gD v 1 ∈ N := fun v hv =>
    hN1 (gD v 1) (gD_right v 1)
      (by rw [gD_left v 1]; exact (pD_mem_pslRange_iff v).2 hv)
  have hN3 : gA (1 : Fˣ) 1 ∈ N :=
    hN1 (gA 1 1) (gA_right 1 1)
      (by rw [gA_left 1 1]; exact (pA_mem_pslRange_iff_of_four_dvd h4dvd 1).2 ⟨1, by simp⟩)
  have hN2' : ∀ v : Fˣ, ¬ IsSquare v → gD v σ₀ ∈ N := by
    obtain ⟨y₀, hy₀, hy₀mem⟩ := hN2
    have hy₁ : ∃ y₁ : Fˣ, ¬ IsSquare y₁ ∧ gD y₁ σ₀ ∈ N := by
      rcases hy₀mem with h | h
      · exact ⟨y₀, hy₀, h⟩
      · refine ⟨y₀⁻¹, ?_, ?_⟩
        · rwa [isSquare_inv]
        · have hprod : gA (1 : Fˣ) 1 * gA y₀ σ₀ = gD y₀⁻¹ σ₀ := by
            rw [gA_mul_gA]
            simp [autU_one_aut]
          rw [← hprod]
          exact N.mul_mem hN3 h
    obtain ⟨y₁, hy₁, hy₁mem⟩ := hy₁
    intro v hv
    have hsq : IsSquare (v * y₁⁻¹) :=
      isSquare_mul_of_not_isSquare h2 hv (by rwa [isSquare_inv])
    have hmem1 : gD (v * y₁⁻¹) 1 ∈ N := hN1sq _ hsq
    have hsplit : gD (v * y₁⁻¹) 1 * gD y₁ σ₀ = gD v σ₀ := by
      rw [gD_mul_gD]
      simp only [autU_one_aut, one_mul]
      rw [mul_assoc, inv_mul_cancel, mul_one]
    rw [← hsplit]
    exact N.mul_mem hmem1 hy₁mem
  refine l1_of_sylow (N := N) (P := stdSylow ξ ψ) (m := 2 ^ padicValNat 2 f) hP ?_ hH hHM hSH hS hy
  intro y' hy'
  obtain ⟨ζ, hζ, hNmem, hlt⟩ :=
    exists_large_order_in_coset (N := N) h2 hξ hc2 he hψo hs hodd harith' hσ₀' hN1sq hN2' hN3 hy'
  exact ⟨ζ, hζ, hNmem, by rwa [hpv]⟩

end L1Gamma

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

