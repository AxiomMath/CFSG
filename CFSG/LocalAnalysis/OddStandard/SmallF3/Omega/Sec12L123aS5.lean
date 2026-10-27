module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Equiv Equiv.Perm Subgroup

private theorem sign_eq_one_iff {X : Type*} [Group X] {n : ℕ} (ρ : X ≃* Equiv.Perm (Fin n))
    (x : X) : Equiv.Perm.sign (ρ x) = 1 ↔ x ∈ Subgroup.closure {y : X | Odd (orderOf y)} := by
  constructor
  · intro hx
    have h1 : ρ x ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.mpr hx
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating] at h1
    have h2 : ρ.symm (ρ x) ∈ Subgroup.map ρ.symm.toMonoidHom
        (Subgroup.closure {σ : Equiv.Perm (Fin n) | σ.IsThreeCycle}) :=
      Subgroup.mem_map_of_mem _ h1
    rw [MonoidHom.map_closure] at h2
    simp only [MulEquiv.symm_apply_apply] at h2
    refine Subgroup.closure_mono ?_ h2
    rintro _ ⟨σ, hσ, rfl⟩
    show Odd (orderOf (ρ.symm σ))
    rw [MulEquiv.orderOf_eq, Equiv.Perm.IsThreeCycle.orderOf hσ]
    exact ⟨1, rfl⟩
  · intro hx
    have hker : Subgroup.closure {y : X | Odd (orderOf y)} ≤
        (Equiv.Perm.sign.comp ρ.toMonoidHom).ker := by
      rw [Subgroup.closure_le]
      intro y hy
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply]
      have hy' : Odd (orderOf y) := hy
      have hpow : (Equiv.Perm.sign (ρ y)) ^ orderOf y = 1 := by
        rw [← map_pow, ← map_pow, pow_orderOf_eq_one, map_one, map_one]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (ρ y)) with h | h
      · exact h
      · rw [h, hy'.neg_one_pow] at hpow
        exact absurd hpow (by decide)
    exact hker hx

theorem sec123_sign_eq {X : Type*} [Group X] {n : ℕ} (ρ σ : X ≃* Equiv.Perm (Fin n)) (x : X) :
    Equiv.Perm.sign (ρ x) = Equiv.Perm.sign (σ x) := by
  have h1 := sign_eq_one_iff ρ x
  have h2 := sign_eq_one_iff σ x
  rcases Int.units_eq_one_or (Equiv.Perm.sign (ρ x)) with h | h <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign (σ x)) with h' | h'
  · rw [h, h']
  · exfalso
    have := h2.mpr (h1.mp h)
    rw [h'] at this
    exact absurd this (by decide)
  · exfalso
    have := h1.mpr (h2.mp h')
    rw [h] at this
    exact absurd this (by decide)
  · rw [h, h']

theorem sec123_normal_odd {X : Type*} [Group X] (e : X ≃* Equiv.Perm (Fin 5)) {K : Subgroup X}
    (hK : K.Normal) (hne : K ≠ ⊥) : ∃ x ∈ K, x ≠ 1 ∧ Odd (orderOf x) := by
  have key : ∀ k : Equiv.Perm (Fin 5), k ≠ 1 → ∃ g : Equiv.Perm (Fin 5),
      k * g * k⁻¹ * g⁻¹ ≠ 1 ∧ ((k * g * k⁻¹ * g⁻¹) ^ 3 = 1 ∨ (k * g * k⁻¹ * g⁻¹) ^ 5 = 1) := by
    decide +kernel
  obtain ⟨⟨k, hkK⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hk1' : e k ≠ 1 := by
    intro h
    apply hk1
    apply Subtype.ext
    exact e.injective (by simpa using h)
  obtain ⟨g', hg1, hg35⟩ := key (e k) hk1'
  set g : X := e.symm g' with hg
  have hxK : k * g * k⁻¹ * g⁻¹ ∈ K := by
    have : k * (g * k⁻¹ * g⁻¹) ∈ K := K.mul_mem hkK (hK.conj_mem _ (K.inv_mem hkK) g)
    simpa [mul_assoc] using this
  have hex : e (k * g * k⁻¹ * g⁻¹) = e k * g' * (e k)⁻¹ * g'⁻¹ := by
    simp [hg]
  refine ⟨k * g * k⁻¹ * g⁻¹, hxK, ?_, ?_⟩
  · intro h
    apply hg1
    rw [← hex, h, map_one]
  · rw [← MulEquiv.orderOf_eq e, hex]
    rcases hg35 with h3 | h5
    · rw [orderOf_eq_prime h3 hg1]
      exact ⟨1, rfl⟩
    · haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      rw [orderOf_eq_prime h5 hg1]
      exact ⟨2, rfl⟩

theorem sec123_swap_of_involution {σ : Equiv.Perm (Fin 5)} (h2 : σ * σ = 1)
    (hs : Equiv.Perm.sign σ = -1) : ∃ a b : Fin 5, a ≠ b ∧ σ = Equiv.swap a b := by
  have key : ∀ σ : Equiv.Perm (Fin 5), σ * σ = 1 → Equiv.Perm.sign σ = -1 →
      ∃ a b : Fin 5, a ≠ b ∧ σ = Equiv.swap a b := by
    decide +kernel
  exact key σ h2 hs

theorem sec123_bijective {X : Type*} [Group X] (e : X ≃* Equiv.Perm (Fin 5))
    {ρ : X →* Equiv.Perm (Fin 5)} (h : Function.Injective ρ ∨ Function.Surjective ρ) :
    Function.Bijective ρ := by
  haveI : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hiff : Function.Injective ρ ↔ Function.Surjective ρ :=
    Finite.injective_iff_surjective_of_equiv e.toEquiv
  rcases h with h | h
  · exact ⟨h, hiff.mp h⟩
  · exact ⟨hiff.mpr h, h⟩

theorem sec123_s0_alg {X : Type*} [Group X] (ρ₁ ρ₂ ρ₃ : X ≃* Equiv.Perm (Fin 5)) :
    ∃ x : X, orderOf x = 2 ∧ ρ₁ x = Equiv.swap 0 1 ∧
      (∃ a b : Fin 5, a ≠ b ∧ ρ₂ x = Equiv.swap a b) ∧ Equiv.Perm.sign (ρ₃ x) = -1 := by
  have h01 : (Equiv.swap (0 : Fin 5) 1) ^ 2 = 1 := by decide
  have h01' : (Equiv.swap (0 : Fin 5) 1) ≠ 1 := by decide
  have hord : orderOf (Equiv.swap (0 : Fin 5) 1) = 2 := orderOf_eq_prime h01 h01'
  have hsgn : Equiv.Perm.sign (Equiv.swap (0 : Fin 5) 1) = -1 := Equiv.Perm.sign_swap (by decide)
  refine ⟨ρ₁.symm (Equiv.swap 0 1), ?_, by simp, ?_, ?_⟩
  · rw [← MulEquiv.orderOf_eq ρ₁.symm.symm, ← hord]
    simp
  · have h2 : Equiv.Perm.sign (ρ₂ (ρ₁.symm (Equiv.swap 0 1))) = -1 := by
      rw [← sec123_sign_eq ρ₁ ρ₂, MulEquiv.apply_symm_apply, hsgn]
    have hord2 : orderOf (ρ₂ (ρ₁.symm (Equiv.swap 0 1))) = 2 := by
      rw [MulEquiv.orderOf_eq ρ₂, MulEquiv.orderOf_eq ρ₁.symm, hord]
    have hsq : ρ₂ (ρ₁.symm (Equiv.swap 0 1)) * ρ₂ (ρ₁.symm (Equiv.swap 0 1)) = 1 := by
      rw [← sq, ← hord2]
      exact pow_orderOf_eq_one _
    exact sec123_swap_of_involution hsq h2
  · rw [← sec123_sign_eq ρ₁ ρ₃, MulEquiv.apply_symm_apply, hsgn]

end CFSG.OddStandard.SmallF3.Omega
