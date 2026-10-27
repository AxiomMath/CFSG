module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26FieldAut
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26L2Arith
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26L2Setup
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26PGLCalc

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.GorensteinWalter CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
open scoped MatrixGroups commutatorElement

theorem l2_data_even {r : ℕ} (hr : 4 ≤ r) {A : Type} [Group A] [Finite A] (T : Subgroup A) [T.Normal]
    (hT : CFSG.ClassicalInvolution.Q3.TA3.SmallL2 ↥T) (hC : Subgroup.centralizer (T : Set A) = ⊥)
    {x b z : A} (hxo : orderOf x = 2 ^ (r - 1)) (hbx : b * x * b⁻¹ = x⁻¹)
    (hbb : b * b = x ^ 2 ^ (r - 2)) (hz : x ^ 2 ^ (r - 2) = z) :
    ∃ (p f : ℕ) (K : Type) (_ : Field K) (_ : Finite K), p.Prime ∧ p ≠ 2 ∧ Nat.card K = p ^ f ∧
      Even f ∧ 13 ≤ p ^ f ∧ Nonempty (↥T ≃* GorensteinWalter.PSL2 K) := by
  classical
  obtain ⟨p, f, K, _, _, Ψ, α, hp, hp2, hf, hKcard, h2, hPSL, hΨz, hΨx, hα, hΨbb, hΨbα, hΨb1,
    hmem, a₀, ha₀T, ha₀z, hΨa₀⟩ := l2_setup_iff hr T hT hC hxo hbx hbb hz
  haveI : Fact p.Prime := ⟨hp⟩
  have hθinj : Function.Injective
      ((Ψ.toMonoidHom : MulAut ↥T →* PGammaL2 K).comp (MulAut.conjNormal : A →* MulAut ↥T)) :=
    Ψ.injective.comp (conjNormal_injective hC)
  have hB'Z : Ψ (MulAut.conjNormal b) * tor (-1) = tor (-1) * Ψ (MulAut.conjNormal b) := by
    rw [← hΨbb, ← mul_assoc]
  obtain ⟨γ, ε, σ, hε, hBe⟩ := exists_decomp h2 hB'Z
  have hσr : (Ψ (MulAut.conjNormal b)).right = σ := by
    have h := congrArg (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)) hBe
    rw [map_mul, map_mul, map_pow, rightHom_tor, rightHom_wref, SemidirectProduct.rightHom_inr,
      one_pow, one_mul, one_mul] at h
    exact h
  have hσ1 : σ ≠ 1 := fun h => hΨb1 (hσr.trans h)
  have hσ2 : σ * σ = 1 := by
    have h := congrArg (SemidirectProduct.rightHom : PGammaL2 K →* (K ≃+* K)) hΨbb
    rw [map_mul, rightHom_tor] at h
    exact hσr ▸ h
  obtain ⟨q, hqq, hq⟩ := fieldAut_invol_eq_pow hσ2 hσ1
  have hBB : (tor γ * wref ^ ε * SemidirectProduct.inr σ : PGammaL2 K) *
      (tor γ * wref ^ ε * SemidirectProduct.inr σ) = tor (-1) := by
    rw [← hBe]; exact hΨbb
  have hBα : (tor γ * wref ^ ε * SemidirectProduct.inr σ : PGammaL2 K) * tor α *
      (tor γ * wref ^ ε * SemidirectProduct.inr σ)⁻¹ = tor α⁻¹ := by
    rw [← hBe]; exact hΨbα
  obtain ⟨h0, h1⟩ := l2_alpha_facts hr hα hε hq hσ2 hBB hBα
  have hNodd : Odd (Nat.card K) := by rw [hKcard]; exact (hp.odd_of_ne_two hp2).pow
  have hqodd : Odd q := by
    rw [← hqq] at hNodd
    exact (Nat.odd_mul.mp hNodd).1
  obtain ⟨hrN, hγN, δ, hδ⟩ := l2_nu_facts hr hα hε hqq hqodd h0 h1
  set N := padicValNat 2 (Nat.card K - 1) with hNdef
  have hN2 : 2 ^ r ∣ Nat.card K - 1 :=
    (pow_dvd_pow 2 hrN).trans (pow_padicValNat_dvd (p := 2) (n := Nat.card K - 1))
  have hNpos : 0 < Nat.card K - 1 := by
    have : 1 < Nat.card K := Finite.one_lt_card
    omega
  have h2r : 2 ^ r ≤ Nat.card K - 1 := Nat.le_of_dvd hNpos hN2
  have h16 : 16 ≤ 2 ^ r := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
  refine ⟨p, f, K, inferInstance, inferInstance, hp, hp2, hKcard, ?_, ?_, hPSL⟩
  ·
    have hq' : q ∣ p ^ f := ⟨q, by rw [← hKcard, ← hqq]⟩
    obtain ⟨a, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hq'
    have h1 : p ^ (a + a) = p ^ f := by rw [pow_add]; exact hqq.trans hKcard
    have h2' : a + a = f := Nat.pow_right_injective hp.two_le h1
    exact ⟨a, h2'.symm⟩
  · rw [← hKcard]
    omega


end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
