module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Set.Card
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.KC.LyBase

open Equiv MulAction

theorem ncard_orbit_mul_card_inf {n : Nat} (K : Subgroup (Perm (Fin n))) (b : Fin n) :
    (orbit K b).ncard * Nat.card ↥(K ⊓ stabilizer (Perm (Fin n)) b) = Nat.card K := by
  have e : Nat.card ↥(K ⊓ stabilizer (Perm (Fin n)) b) = Nat.card (stabilizer K b) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
        invFun := fun g => ⟨g.1.1, g.1.2, g.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have : Fintype K := Fintype.ofFinite _
  have : Fintype (orbit K b) := Fintype.ofFinite _
  have : Fintype (stabilizer K b) := Fintype.ofFinite _
  have h := card_orbit_mul_card_stabilizer_eq_card_group K b
  rw [e, ← Nat.card_coe_set_eq]
  simpa only [Nat.card_eq_fintype_card] using h

theorem eq_one_of_fix3 {n : Nat} (H : Subgroup (Perm (Fin n))) (β₀ β₁ β₂ : Fin n)
    {m₀ m₁ m₂ : Nat} (hm : 0 < m₀ * m₁ * m₂) (hH : Nat.card H ≤ m₀ * m₁ * m₂)
    (h₀ : m₀ ≤ (orbit H β₀).ncard)
    (h₁ : m₁ ≤ (orbit ↥(H ⊓ stabilizer (Perm (Fin n)) β₀) β₁).ncard)
    (h₂ : m₂ ≤ (orbit ↥(H ⊓ stabilizer (Perm (Fin n)) β₀ ⊓ stabilizer (Perm (Fin n)) β₁)
      β₂).ncard)
    {g : Perm (Fin n)} (hg : g ∈ H) (g₀ : g β₀ = β₀) (g₁ : g β₁ = β₁) (g₂ : g β₂ = β₂) :
    g = 1 := by
  have e₀ := ncard_orbit_mul_card_inf H β₀
  have e₁ := ncard_orbit_mul_card_inf (H ⊓ stabilizer (Perm (Fin n)) β₀) β₁
  have e₂ := ncard_orbit_mul_card_inf
    (H ⊓ stabilizer (Perm (Fin n)) β₀ ⊓ stabilizer (Perm (Fin n)) β₁) β₂
  set K₁ := H ⊓ stabilizer (Perm (Fin n)) β₀
  set K₂ := K₁ ⊓ stabilizer (Perm (Fin n)) β₁
  set K₃ := K₂ ⊓ stabilizer (Perm (Fin n)) β₂
  have hpos : 0 < Nat.card K₃ := Nat.card_pos
  have key : m₀ * m₁ * m₂ * Nat.card K₃ ≤ m₀ * m₁ * m₂ := by
    calc m₀ * m₁ * m₂ * Nat.card K₃
        ≤ (orbit H β₀).ncard * (orbit K₁ β₁).ncard * (orbit K₂ β₂).ncard * Nat.card K₃ := by
          gcongr
      _ = Nat.card H := by rw [← e₀, ← e₁, ← e₂]; ring
      _ ≤ m₀ * m₁ * m₂ := hH
  have h1 : Nat.card K₃ ≤ 1 := by
    by_contra hc
    have : m₀ * m₁ * m₂ * 2 ≤ m₀ * m₁ * m₂ * Nat.card K₃ := Nat.mul_le_mul_left _ (by omega)
    omega
  have : Fintype K₃ := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at h1
  have hs : Subsingleton K₃ := Fintype.card_le_one_iff_subsingleton.1 h1
  have hgK : g ∈ K₃ := ⟨⟨⟨hg, g₀⟩, g₁⟩, g₂⟩
  have := Subsingleton.elim (⟨g, hgK⟩ : K₃) ⟨1, K₃.one_mem⟩
  exact congrArg Subtype.val this

end CFSG.KC.LyBase

end
