module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4Fix

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG CFSG.ClassicalInvolution QuaternionGroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

theorem noQ8Fix_of_dichotomy_pow {K : Type} [Group K] {H : Subgroup K} (T : Set (MulAut K))
    (hT : ∀ α ∈ T, ∀ β ∈ T, α * β = β * α)
    (h : ∀ α : MulAut K, (∀ j ∈ H, α j = j) → α ^ 8 = 1 → α ∈ T ∨ α * α = 1) :
    NoQ8Fix K H := by
  intro ψ hψ hfix
  have h8 : ∀ q : QuaternionGroup 2, ψ q ^ 8 = 1 := fun q => by
    rw [← map_pow, orderOf_dvd_iff_pow_eq_one.mp (orderOf_q8_dvd q), map_one]
  have hsq : ∀ q : QuaternionGroup 2, q * q ≠ 1 → ψ q ∈ T := fun q hq => by
    rcases h (ψ q) (hfix q) (h8 q) with h1 | h1
    · exact h1
    · exact absurd (hψ (by rw [map_mul, h1, map_one])) hq
  have := hT _ (hsq (a 1) (by decide)) _ (hsq (xa 0) (by decide))
  rw [← map_mul, ← map_mul] at this
  exact absurd (hψ this) (by decide)

theorem noQ8Outer_of_commutator {P : Type*} [Group P]
    (h : ∀ α β : MulAut P, α ^ 4 ∈ inner P → β ^ 4 ∈ inner P → α ^ 2 ∉ inner P →
      β ^ 2 ∉ inner P → ⁅α, β⁆ ∈ inner P) :
    ∀ φ : QuaternionGroup 2 →* Outer P, ¬ Function.Injective φ := by
  intro φ hφ
  obtain ⟨α, hα⟩ := QuotientGroup.mk_surjective (φ (a 1))
  obtain ⟨β, hβ⟩ := QuotientGroup.mk_surjective (φ (xa 0))
  have h4 : ∀ (x : QuaternionGroup 2) (γ : MulAut P), (γ : Outer P) = φ x → x ^ 4 = 1 →
      γ ^ 4 ∈ inner P := by
    intro x γ hγ hx
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hγ, ← map_pow, hx, map_one]
  have h2 : ∀ (x : QuaternionGroup 2) (γ : MulAut P), (γ : Outer P) = φ x → x ^ 2 ≠ 1 →
      γ ^ 2 ∉ inner P := by
    intro x γ hγ hx hin
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hγ, ← map_pow] at hin
    exact hx (hφ (hin.trans (map_one φ).symm))
  have hc := h α β (h4 _ _ hα (by decide)) (h4 _ _ hβ (by decide)) (h2 _ _ hα (by decide))
    (h2 _ _ hβ (by decide))
  rw [← QuotientGroup.eq_one_iff, commutatorElement_def, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
    hα, hβ] at hc
  have hab : φ (a 1 * xa 0) = φ (xa 0 * a 1) := by
    rw [map_mul, map_mul]
    calc φ (a 1) * φ (xa 0) = φ (a 1) * φ (xa 0) * (φ (a 1))⁻¹ * (φ (xa 0))⁻¹ *
        (φ (xa 0) * φ (a 1)) := by group
      _ = φ (xa 0) * φ (a 1) := by rw [hc, one_mul]
  exact absurd (hφ hab) (by decide)

theorem noQ8Outer_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ φ : QuaternionGroup 2 →* Outer Y, ¬ Function.Injective φ) :
    ∀ φ : QuaternionGroup 2 →* Outer X, ¬ Function.Injective φ := fun φ hφ =>
  h ((CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toMonoidHom.comp φ)
    ((CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).injective.comp hφ)

end CFSG.ClassicalInvolution.Q3.TA3
