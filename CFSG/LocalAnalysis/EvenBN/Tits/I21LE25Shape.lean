module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LModE

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup

section Shape

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {B : Type*} [Group B]

@[expose] def E25Shape (ρ : B →* (V ≃ₗ[ZMod 2] V)) (x t : B) : Prop :=
  Nat.card (Jbar ρ x) = 25 ∧
    ∃ V₁ V₂ : Submodule (ZMod 2) V, finrank (ZMod 2) V₁ = 4 ∧ IsCompl V₁ V₂ ∧
      V₂ = V₁.map (ρ t : V →ₗ[ZMod 2] V) ∧ (∀ g ∈ Jbar ρ x, Stable g V₁ ∧ Stable g V₂) ∧
      (∀ b : B, (V₁.map (ρ b : V →ₗ[ZMod 2] V) = V₁ ∧ V₂.map (ρ b : V →ₗ[ZMod 2] V) = V₂) ∨
        (V₁.map (ρ b : V →ₗ[ZMod 2] V) = V₂ ∧ V₂.map (ρ b : V →ₗ[ZMod 2] V) = V₁)) ∧
      (∀ g ∈ Jbar ρ x, (∃ k : ℕ, ∀ v ∈ V₁, g v = (ρ x) ^ k • v) ∧
        ∃ k : ℕ, ∀ v ∈ V₂, g v = (ρ x) ^ k • v) ∧
      ∃ K₁ K₂ : Subgroup (V ≃ₗ[ZMod 2] V), K₁ ≤ Jbar ρ x ∧ K₂ ≤ Jbar ρ x ∧ K₁ ⊓ K₂ = ⊥ ∧
        K₁ ⊔ K₂ = Jbar ρ x ∧ Nat.card K₁ = 5 ∧ Nat.card K₂ = 5 ∧
        (∀ v : V, v ∈ V₁ ↔ ∀ g ∈ K₁, g v = v) ∧ (∀ v : V, v ∈ V₂ ↔ ∀ g ∈ K₂, g v = v)

theorem E25Shape.of_hypM [Finite B] {ρ : B →* (V ≃ₗ[ZMod 2] V)} {x t z h : B}
    (H : HypM ρ x t z h) (hab : ∀ a ∈ Jbar ρ x, ∀ b ∈ Jbar ρ x, a * b = b * a) :
    E25Shape ρ x t :=
  module_E25_abs H hab

end Shape

section ToHypM

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Y : Type*} [Group Y]
  {ρ : Y →* (V ≃ₗ[ZMod 2] V)} {t u x h : Y}

theorem HypYW.toHypM (H : HypYW ρ t u x h) : HypM ρ x t (u ^ 2) h where
  dim := H.dim
  ord_x := by rw [orderOf_injective ρ H.inj x]; exact H.ord_x
  fix := H.fix
  t_sq := by
    have h2 : t * t = 1 := by rw [← pow_two]; exact H.sec.orderOf_t ▸ pow_orderOf_eq_one t
    rw [← map_mul, h2, map_one]
  tx := H.tx
  zx := by
    have h5 : x ^ 5 = 1 := by rw [← H.ord_x]; exact pow_orderOf_eq_one x
    have hx4 : (x ^ 4) = x⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, h5]
    have key : ∀ m : ℕ, u * x * u⁻¹ = x ^ m → u ^ 2 * x * (u ^ 2)⁻¹ = x ^ (m * m) := by
      intro m hm
      calc u ^ 2 * x * (u ^ 2)⁻¹ = u * (u * x * u⁻¹) * u⁻¹ := by
            rw [pow_two, mul_inv_rev]
            simp only [mul_assoc]
        _ = u * x ^ m * u⁻¹ := by rw [hm]
        _ = (u * x * u⁻¹) ^ m := conj_pow.symm
        _ = (x ^ m) ^ m := by rw [hm]
        _ = x ^ (m * m) := (pow_mul x m m).symm
    rcases H.ux with hm | hm
    · rw [key 2 hm]
      exact hx4
    · rw [key 3 hm]
      show x ^ 9 = x⁻¹
      rw [show 9 = 5 + 4 from rfl, pow_add, h5, one_mul]
      exact hx4
  ht := H.fuse

end ToHypM

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
