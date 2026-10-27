module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Assemble

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Subgroup

variable {Γ : Type*} [Group Γ]

theorem comm_of_commutator_eq_bot {X Y : Subgroup Γ} (h : ⁅X, Y⁆ = ⊥) :
    ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
  intro x hx y hy
  have := Subgroup.commutator_mem_commutator hx hy
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

theorem pow_three_of_mem {Z : Subgroup Γ} [Finite Z] (hZ : Nat.card Z ∣ 3) {z : Γ} (hz : z ∈ Z) :
    z ^ 3 = 1 := by
  have h1 : orderOf (⟨z, hz⟩ : Z) ∣ Nat.card Z := orderOf_dvd_natCard _
  have h2 := pow_orderOf_eq_one (⟨z, hz⟩ : Z)
  have h3 : (⟨z, hz⟩ : Z) ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := h1.trans hZ
    rw [hk, pow_mul, h2, one_pow]
  exact congrArg Subtype.val h3

variable {τ : Γ →* Γ} {X : Subgroup Γ}

theorem mem_map_of_mem_inv {x : Γ} (hx : x ∈ X) : τ x ∈ X.map τ := ⟨x, hx, rfl⟩

theorem mem_of_mem_map (hττ : ∀ g, τ (τ g) = g) {y : Γ} (hy : y ∈ X.map τ) : τ y ∈ X := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [hττ]; exact hx

theorem exists_coboundary [Finite Γ] (hττ : ∀ g, τ (τ g) = g) (h1 : X ⊔ X.map τ = ⊤)
    (h2 : ⁅X, X.map τ⁆ = ⊥) (h3 : Nat.card (X ⊓ X.map τ : Subgroup Γ) ∣ 3) {s : Γ}
    (hs : s * τ s = 1) : ∃ γ, s = γ * (τ γ)⁻¹ := by
  have hc := comm_of_commutator_eq_bot h2
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_sup_of_commute hc (h1 ▸ Subgroup.mem_top s)
  have hτx : τ x ∈ X.map τ := mem_map_of_mem_inv hx
  have hτy : τ y ∈ X := mem_of_mem_map hττ hy
  obtain ⟨z, hzdef⟩ : ∃ z, z = x * τ y := ⟨_, rfl⟩
  have hzX : z ∈ X := hzdef ▸ mul_mem hx hτy
  have hz' : z = (y * τ x)⁻¹ := by
    rw [map_mul] at hs
    have e : x * y * (τ x * τ y) = (x * τ y) * (y * τ x) := by
      have := hc (τ y) hτy (y * τ x) (mul_mem hy hτx)
      calc x * y * (τ x * τ y) = x * ((y * τ x) * τ y) := by group
        _ = x * (τ y * (y * τ x)) := by rw [this]
        _ = (x * τ y) * (y * τ x) := by group
    rw [e] at hs
    rw [hzdef]
    exact eq_inv_of_mul_eq_one_left hs
  have hzY : z ∈ X.map τ := by rw [hz']; exact inv_mem (mul_mem hy hτx)
  have hz3 : z ^ 3 = 1 := pow_three_of_mem h3 ⟨hzX, hzY⟩
  have hzc : ∀ g, z * g = g * z := fun g => by
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hc (h1 ▸ Subgroup.mem_top g)
    have e1 : z * a = a * z := (hc a ha z hzY).symm
    have e2 : z * b = b * z := hc z hzX b hb
    calc z * (a * b) = (z * a) * b := by group
      _ = a * (z * b) := by rw [e1]; group
      _ = a * b * z := by rw [e2]; group
  have hτz : τ z = z⁻¹ := by
    have e1 : τ z = τ x * y := by rw [hzdef, map_mul, hττ]
    have e2 : τ x = y⁻¹ * z⁻¹ := by
      rw [hz', inv_inv]; group
    rw [e1, e2]
    have := hzc y
    calc y⁻¹ * z⁻¹ * y = y⁻¹ * (z⁻¹ * y) := by group
      _ = y⁻¹ * (y * z⁻¹) := by
        congr 1
        calc z⁻¹ * y = z⁻¹ * (y * z) * z⁻¹ := by group
          _ = z⁻¹ * (z * y) * z⁻¹ := by rw [this]
          _ = y * z⁻¹ := by group
      _ = z⁻¹ := by group
  refine ⟨z⁻¹ * y, ?_⟩
  have hzi : z⁻¹ = z * z := by
    have : z * (z * z) = z ^ 3 := (pow_three z).symm
    rw [hz3] at this
    exact (eq_inv_of_mul_eq_one_right this).symm
  have hyc : y * (τ y)⁻¹ = (τ y)⁻¹ * y := (hc _ (inv_mem hτy) y hy).symm
  have hx' : x = z * (τ y)⁻¹ := by rw [hzdef]; group
  rw [map_mul, map_inv, hτz, inv_inv, hx']
  have hzyc : ∀ g, z⁻¹ * g = g * z⁻¹ := fun g => by
    have := hzc g
    calc z⁻¹ * g = z⁻¹ * (g * z) * z⁻¹ := by group
      _ = z⁻¹ * (z * g) * z⁻¹ := by rw [this]
      _ = g * z⁻¹ := by group
  have hzz : z⁻¹ * z⁻¹ = z := by
    rw [hzi]
    have : z * z * (z * z) = z ^ 3 * z := by rw [pow_three]; group
    rw [this, hz3, one_mul]
  have e1 : z⁻¹ * y * (z * τ y)⁻¹ = z⁻¹ * (y * (τ y)⁻¹) * z⁻¹ := by group
  rw [e1, hyc, mul_assoc z⁻¹, ← hzyc ((τ y)⁻¹ * y), ← mul_assoc, hzz]
  group

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
