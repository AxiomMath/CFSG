module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.GLS.SP

open scoped Pointwise

theorem card_sup_of_inf_eq_bot {G : Type*} [Group G] {K A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (K : Set G)) (hKA : K ⊓ A = ⊥) :
    Nat.card ↥(K ⊔ A) = Nat.card K * Nat.card A := by
  have hset : ((K ⊔ A : Subgroup G) : Set G) = (K : Set G) * (A : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K A hA
  let f : K × A → G := fun p => (p.1 : G) * (p.2 : G)
  have hf : Function.Injective f := by
    rintro ⟨k, a⟩ ⟨k', a'⟩ h
    have h1 : (k' : G)⁻¹ * k = a' * (a : G)⁻¹ := by
      have : (k : G) * a = k' * a' := h
      calc (k' : G)⁻¹ * k = (k' : G)⁻¹ * (k * a) * (a : G)⁻¹ := by group
        _ = (k' : G)⁻¹ * (k' * a') * (a : G)⁻¹ := by rw [this]
        _ = a' * (a : G)⁻¹ := by group
    have h2 : (k' : G)⁻¹ * k ∈ K ⊓ A := ⟨K.mul_mem (K.inv_mem k'.2) k.2, by
      rw [h1]; exact A.mul_mem a'.2 (A.inv_mem a.2)⟩
    rw [hKA, Subgroup.mem_bot] at h2
    have hk : k = k' := (Subtype.ext (inv_mul_eq_one.1 h2)).symm
    subst hk
    have : (a' : G) * (a : G)⁻¹ = 1 := by rw [← h1]; exact h2
    have ha : a = a' := Subtype.ext (mul_inv_eq_one.1 this).symm
    rw [ha]
  have hrange : Set.range f = ((K ⊔ A : Subgroup G) : Set G) := by
    rw [hset]
    ext x
    constructor
    · rintro ⟨⟨k, a⟩, rfl⟩
      exact Set.mem_mul.2 ⟨k, k.2, a, a.2, rfl⟩
    · intro hx
      obtain ⟨k, hk, a, ha, rfl⟩ := Set.mem_mul.1 hx
      exact ⟨⟨⟨k, hk⟩, ⟨a, ha⟩⟩, rfl⟩
  calc Nat.card ↥(K ⊔ A) = Nat.card (Set.range f) := by rw [hrange]; rfl
    _ = Nat.card (K × A) := (Nat.card_congr (Equiv.ofInjective f hf)).symm
    _ = Nat.card K * Nat.card A := Nat.card_prod _ _

theorem gen_of_order {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {G₀ A : Subgroup G}
    (hG₀ : G₀ ≠ ⊥) (hA : A ≤ Subgroup.normalizer (G₀ : Set G)) (hAG : G₀ ⊓ A = ⊥)
    (hcard : Nat.card G ≤ Nat.card G₀ * Nat.card A) : G₀ = ⊤ := by
  have h1 := card_sup_of_inf_eq_bot hA hAG
  have h2 : G₀ ⊔ A = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    exact le_antisymm (Subgroup.card_le_card_group _) (h1 ▸ hcard)
  have hN : Subgroup.normalizer (G₀ : Set G) = ⊤ := by
    rw [eq_top_iff, ← h2]
    exact sup_le Subgroup.le_normalizer hA
  have : G₀.Normal := Subgroup.normalizer_eq_top_iff.1 hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal G₀ with h | h
  · exact absurd h hG₀
  · exact h

end CFSG.GH74.GLS.SP
