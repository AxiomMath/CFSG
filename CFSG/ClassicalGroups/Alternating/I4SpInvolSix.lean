module

public import CFSG.ClassicalGroups.Alternating.I4SpInvolBlock
public import CFSG.ClassicalGroups.Alternating.I4SpInvolConj

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open Module

variable {K N : Type*} [Field K] [AddCommGroup N] [Module K N] {BN : BilinForm K N}

theorem Gsp.Block.mul_self_tau_mul {t τ h : Gsp BN} {X : Submodule K N}
    (hb : t.Block X τ h) (ht : t * t = 1) : (τ * t) * (τ * t) = 1 := by
  obtain ⟨u, hu⟩ : ∃ u : Gsp BN, u = τ * t := ⟨_, rfl⟩
  rw [← hu]
  obtain ⟨huτ, -⟩ := hb.commute u (fun x hx => hu ▸ hb.fixes x hx)
  have htτu : t = τ * u := by rw [hu, ← mul_assoc, hb.tau_mul_self, one_mul]
  have h1 : t * t = τ * (u * τ) * u := by rw [htτu]; group
  rw [huτ.eq, ← mul_assoc, hb.tau_mul_self, one_mul] at h1
  exact h1.symm.trans ht

theorem orderOf_mul_conj_eq_six_of_block [CharP K 2] {t τ h k : Gsp BN} {X : Submodule K N}
    (hb : t.Block X τ h) (ht : t * t = 1) (hkfix : ∀ x ∈ X, k.app x = x)
    (hkne : k * (τ * t) * k⁻¹ ≠ τ * t) (hkcomm : Commute (τ * t) (k * (τ * t) * k⁻¹)) :
    orderOf (t * ((h * k) * t * (h * k)⁻¹)) = 6 := by
  obtain ⟨u, hu⟩ : ∃ u : Gsp BN, u = τ * t := ⟨_, rfl⟩
  rw [← hu] at hkne hkcomm
  have huu : u * u = 1 := hu ▸ hb.mul_self_tau_mul ht
  have hufix : ∀ x ∈ X, u.app x = x := fun x hx => hu ▸ hb.fixes x hx
  obtain ⟨huτ, huh⟩ := hb.commute u hufix
  have htτu : t = τ * u := by rw [hu, ← mul_assoc, hb.tau_mul_self, one_mul]
  obtain ⟨hkτ, hkh⟩ := hb.commute k hkfix
  obtain ⟨u', hu'⟩ : ∃ u' : Gsp BN, u' = k * u * k⁻¹ := ⟨_, rfl⟩
  rw [← hu'] at hkne hkcomm
  have hu'fix : ∀ x ∈ X, u'.app x = x := by
    have hmem : u' ∈ Gsp.fixator (BN := BN) (X : Set N) := by
      rw [hu']
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkfix hufix) (Subgroup.inv_mem _ hkfix)
    exact hmem
  obtain ⟨hu'τ, hu'h⟩ := hb.commute u' hu'fix
  have hu'u' : u' * u' = 1 := by
    rw [hu']
    calc k * u * k⁻¹ * (k * u * k⁻¹) = k * (u * u) * k⁻¹ := by group
      _ = 1 := by rw [huu]; group
  have hconj : (h * k) * t * (h * k)⁻¹ = (h * τ * h⁻¹) * u' := by
    have e1 : (h * k) * t * (h * k)⁻¹ = h * (k * τ * u * k⁻¹) * h⁻¹ := by rw [htτu]; group
    have e2 : k * τ * u * k⁻¹ = τ * u' := by
      rw [hkτ.eq, hu']
      group
    rw [e1, e2]
    have e3 : h * (τ * u') * h⁻¹ = h * τ * h⁻¹ * (h * u' * h⁻¹) := by group
    have e4 : h * u' * h⁻¹ = u' := by
      rw [← hu'h.eq]
      group
    rw [e3, e4]
  have hcomm_h : Commute u (h * τ * h⁻¹) :=
    (huh.mul_right huτ).mul_right huh.inv_right
  have hcomm_h' : Commute u' (h * τ * h⁻¹) :=
    (hu'h.mul_right hu'τ).mul_right hu'h.inv_right
  have hprod : t * ((h * k) * t * (h * k)⁻¹) = (τ * (h * τ * h⁻¹)) * (u * u') := by
    rw [hconj, htτu]
    calc τ * u * (h * τ * h⁻¹ * u') = τ * (u * (h * τ * h⁻¹)) * u' := by group
      _ = τ * ((h * τ * h⁻¹) * u) * u' := by rw [hcomm_h.eq]
      _ = (τ * (h * τ * h⁻¹)) * (u * u') := by group
  rw [hprod]
  have hA : Commute (u * u') (τ * (h * τ * h⁻¹)) :=
    ((huτ.mul_right hcomm_h)).mul_left (hu'τ.mul_right hcomm_h')
  have hB2 : orderOf (u * u') = 2 := by
    have hsq : (u * u') ^ 2 = 1 := by
      calc (u * u') ^ 2 = u * (u' * u) * u' := by rw [sq]; group
        _ = u * (u * u') * u' := by rw [← hkcomm.eq]
        _ = (u * u) * (u' * u') := by group
        _ = 1 := by rw [huu, hu'u', one_mul]
    have hne : u * u' ≠ 1 := by
      intro h1
      apply hkne
      have : u' = u⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact inv_eq_of_mul_eq_one_right huu
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hsq hne
  rw [hA.symm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hb.order_three, hB2]; decide),
    hb.order_three, hB2]

theorem exists_conj_orderOf_eq_six [CharP K 2] [Finite K] (hq : 4 ≤ Nat.card K)
    (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate) {t : Gsp BN} (ht : t * t = 1) (ht1 : t ≠ 1)
    (hT : finrank K (LinearMap.range
      (((t : LinearMap.GeneralLinearGroup K N) : N →ₗ[K] N) - 1)) ≠ 1)
    (hA2 : ¬ ∃ a c, BN a c = 0 ∧ LinearIndependent K ![a, c] ∧ t = lineElt hBN a c) :
    ∃ g : Gsp BN, orderOf (t * (g * t * g⁻¹)) = 6 := by
  obtain ⟨X, τ, h, hb, hty⟩ := exists_block hBN hBNnd ht ht1
  have hu1 : τ * t ≠ 1 := fun h1 => by
    rcases hty h1 with h2 | h2
    · exact hT h2
    · exact hA2 h2
  obtain ⟨k, hkfix, hkne, hkcomm⟩ := exists_conj_commute hq hBN hBNnd hb.isCompl
    (hb.mul_self_tau_mul ht) hu1 fun x hx => hb.fixes x hx
  exact ⟨h * k, orderOf_mul_conj_eq_six_of_block hb ht hkfix hkne hkcomm⟩

end CFSG.ClassicalGroups.Alternating
