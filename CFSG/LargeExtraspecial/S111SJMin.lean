module

public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.LinearAlgebra.SL2MinimalFaithful
public import CFSG.GH74.Uniqueness.Bender.Models

public section

namespace CFSG.LargeExtraspecial.S11

open Module CFSG.GH74.Uniqueness.Bender

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]


@[expose] noncomputable def toMulRep {K : Type*} [Group K] (ρ : K →* (V ≃ₗ[ZMod 2] V)) :
    K →* MulAut (Multiplicative V) where
  toFun k := AddEquiv.toMultiplicative (ρ k).toAddEquiv
  map_one' := by
    ext v
    change Multiplicative.ofAdd (ρ 1 (Multiplicative.toAdd v)) = v
    rw [map_one, LinearEquiv.coe_one, id_eq, ofAdd_toAdd]
  map_mul' k k' := by
    ext v
    change Multiplicative.ofAdd (ρ (k * k') (Multiplicative.toAdd v)) =
      Multiplicative.ofAdd (ρ k (ρ k' (Multiplicative.toAdd v)))
    rw [map_mul, LinearEquiv.mul_apply]

theorem le_finrank_of_primitive_prime {K : Type*} [Group K] [Finite K]
    (ρ : K →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ) {ℓ m : ℕ} (hℓ : ℓ.Prime)
    (hℓK : ℓ ∣ Nat.card K) (hm0 : 0 < m) (hm : ℓ ∣ 2 ^ m - 1)
    (hprim : ∀ k : ℕ, 0 < k → k < m → ¬ ℓ ∣ 2 ^ k - 1) : m ≤ finrank (ZMod 2) V := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite V := Module.finite_of_finite (ZMod 2)
  set d := finrank (ZMod 2) V with hd
  have hV : Nat.card (Multiplicative V) = 2 ^ d := by
    rw [Nat.card_congr Multiplicative.toAdd, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod]
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' ℓ hℓK
  have hρh : toMulRep ρ h ≠ 1 := by
    intro h1
    have h2 : ρ h = 1 := by
      ext v
      have := congrArg (fun σ : MulAut (Multiplicative V) => σ (Multiplicative.ofAdd v)) h1
      exact this
    have h3 : h = 1 := hρ (by rw [h2, map_one])
    rw [h3, orderOf_one] at hh
    exact hℓ.one_lt.ne hh
  obtain ⟨e, hed, hdvd⟩ := CFSG.SL2MinimalFaithful.exists_dvd_pow_sub_pow Nat.prime_two hℓ
    (toMulRep ρ) hh hρh hV
  have hfac : 2 ^ d - 2 ^ e = 2 ^ e * (2 ^ (d - e) - 1) := by
    rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hed.le]
  rw [hfac] at hdvd
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 2 ^ m := dvd_pow_self 2 hm0.ne'
    have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have h3 := Nat.dvd_sub h1 hm
    rw [Nat.sub_sub_self h2] at h3
    exact absurd (Nat.le_of_dvd one_pos h3) (by norm_num)
  have hℓp : ¬ ℓ ∣ 2 ^ e := fun h' =>
    hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow h'))
  have h1 : ℓ ∣ 2 ^ (d - e) - 1 :=
    Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓp) hdvd
  by_contra hlt
  push Not at hlt
  exact hprim (d - e) (by omega) (by omega) h1

theorem two_mul_le_finrank_of_benderType {K : Type} [Group K]
    [Finite K] (ρ : K →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ) {n i e : ℕ}
    (hB : BenderType (K ⧸ Subgroup.center K) n i e) (h6 : 2 * i * n ≠ 6) :
    2 * i * n ≤ finrank (ZMod 2) V := by
  obtain ⟨hi, hn⟩ := hB.two_le
  have h2 : 2 ≤ 2 * i * n := by nlinarith
  obtain ⟨ℓ, hℓ, hℓdvd, hprim⟩ :=
    CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (2 * i * n) h2 h6
  have hsplit : 2 ^ (2 * i * n) - 1 = (2 ^ (i * n) - 1) * ((2 ^ n) ^ i + 1) := by
    have hx : (2 ^ n) ^ i = 2 ^ (i * n) := by rw [← pow_mul, mul_comm]
    rw [hx, show 2 * i * n = 2 * (i * n) by ring, pow_mul']
    have h1 : 1 ≤ 2 ^ (i * n) := Nat.one_le_two_pow
    generalize 2 ^ (i * n) = x at h1 ⊢
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have hℓ1 : ¬ ℓ ∣ 2 ^ (i * n) - 1 := hprim (i * n) (by positivity) (by nlinarith)
  have hℓ2 : ℓ ∣ (2 ^ n) ^ i + 1 :=
    ((Nat.Prime.dvd_mul hℓ).mp (hsplit ▸ hℓdvd)).resolve_left hℓ1
  have hℓK : ℓ ∣ Nat.card K := by
    refine (hℓ2.trans ?_).trans (Subgroup.card_quotient_dvd_card (Subgroup.center K))
    rw [hB.card_eq]
    exact dvd_mul_right _ _
  exact le_finrank_of_primitive_prime ρ hρ hℓ hℓK (by positivity) hℓdvd hprim

end CFSG.LargeExtraspecial.S11
