module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Tactic.Group

public section

namespace MonoidHom

variable {G H : Type*} [Group G] [Group H]

theorem injective_of_simple_normal (φ : G →* H) (T : Subgroup G) [T.Normal] [IsSimpleGroup T]
    (hC : Subgroup.centralizer (T : Set G) = ⊥) (hφ : ∃ t ∈ T, φ t ≠ 1) :
    Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.subgroupOf T) with h | h
  · rw [eq_bot_iff, ← hC]
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h1 : t * n * t⁻¹ * n⁻¹ ∈ φ.ker := by
      have := (inferInstance : φ.ker.Normal).conj_mem n hn t
      exact φ.ker.mul_mem this (φ.ker.inv_mem hn)
    have h2 : t * n * t⁻¹ * n⁻¹ ∈ T := by
      have := (inferInstance : T.Normal).conj_mem t⁻¹ (T.inv_mem ht) n
      have e : t * n * t⁻¹ * n⁻¹ = t * (n * t⁻¹ * n⁻¹) := by group
      rw [e]; exact T.mul_mem ht this
    have h3 : (⟨_, h2⟩ : T) ∈ φ.ker.subgroupOf T := h1
    rw [h, Subgroup.mem_bot] at h3
    have h4 : t * n * t⁻¹ * n⁻¹ = 1 := congrArg Subtype.val h3
    calc t * n = t * n * t⁻¹ * n⁻¹ * (n * t) := by group
      _ = n * t := by rw [h4, one_mul]
  · obtain ⟨t, ht, hφt⟩ := hφ
    have : (⟨t, ht⟩ : T) ∈ φ.ker.subgroupOf T := h ▸ Subgroup.mem_top _
    exact absurd this hφt

theorem bijective_of_simple_normal [Finite G] [Finite H] (φ : G →* H) (T : Subgroup G)
    [T.Normal] [IsSimpleGroup T] (hC : Subgroup.centralizer (T : Set G) = ⊥) (hT : T ≠ ⊤)
    (hφ : ∃ t ∈ T, φ t ≠ 1) (hcard : Nat.card H ≤ 2 * Nat.card T) : Function.Bijective φ := by
  refine (injective_of_simple_normal φ T hC hφ).bijective_of_nat_card_le ?_
  have h1 : T.index ≠ 1 := mt Subgroup.index_eq_one.mp hT
  have h0 : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have := T.card_mul_index
  have h2 : 2 ≤ T.index := by omega
  calc Nat.card H ≤ 2 * Nat.card T := hcard
    _ ≤ T.index * Nat.card T := Nat.mul_le_mul_right _ h2
    _ = Nat.card G := by rw [mul_comm]; exact this

end MonoidHom
