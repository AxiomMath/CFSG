module

public import CFSG.GroupTheory.SmallFixedTwoGroup.InvertedAverage

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

variable {G : Type*} [Group G]

theorem translate_mul_self {θ : MulAut G} (hθ : θ * θ = 1) {x : G} (hx : θ x = x⁻¹) :
    (MulAut.conj x * θ) * (MulAut.conj x * θ) = 1 := by
  have hθθ : ∀ g, θ (θ g) = g := fun g => by
    rw [← MulAut.mul_apply, hθ, MulAut.one_apply]
  ext g
  simp only [MulAut.mul_apply, MulAut.one_apply, MulAut.conj_apply, map_mul, map_inv, hθθ, hx]
  group

theorem translate_apply_eq_inv_iff {θ : MulAut G} {x : G} (hx : θ x = x⁻¹) (y : G) :
    (MulAut.conj x * θ) y = y⁻¹ ↔ θ (y * x) = (y * x)⁻¹ := by
  have key : ∀ a b : G, x * a * x⁻¹ = b ↔ a * x⁻¹ = x⁻¹ * b := by
    intro a b
    constructor
    · intro h
      have := congrArg (fun t => x⁻¹ * t) h
      simpa [mul_assoc] using this
    · intro h
      have := congrArg (fun t => x * t) h
      simpa [mul_assoc] using this
  rw [MulAut.mul_apply, MulAut.conj_apply]
  rw [map_mul, hx, mul_inv_rev]
  exact key (θ y) y⁻¹

theorem card_inverted_translate {θ : MulAut G} {x : G} (hx : θ x = x⁻¹) :
    Nat.card {g : G // (MulAut.conj x * θ) g = g⁻¹} = Nat.card {g : G // θ g = g⁻¹} :=
  Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulRight x)
    (fun y => translate_apply_eq_inv_iff hx y))

theorem exists_inverted_translate [Finite G] {θ : MulAut G} (H : Subgroup G) :
    ∃ x : G, θ x = x⁻¹ ∧
      Nat.card H * Nat.card {g : G // θ g = g⁻¹} ≤
        Nat.card G * Nat.card {h : H // (MulAut.conj x * θ) (h : G) = (h : G)⁻¹} := by
  let S : Set G := {g | θ g = g⁻¹}
  have hS : S.Nonempty := ⟨1, by simp [S]⟩
  obtain ⟨x, hxS, hxcard⟩ := exists_mem_card_mul_le_card_coset_inter H S hS
  have hx : θ x = x⁻¹ := hxS
  refine ⟨x, hx, ?_⟩
  have hS_eq : Nat.card S = Nat.card {g : G // θ g = g⁻¹} := rfl
  rw [hS_eq] at hxcard
  have heq : Nat.card {y : G // y ∈ S ∧ y * x⁻¹ ∈ H} =
      Nat.card {h : H // (MulAut.conj x * θ) (h : G) = (h : G)⁻¹} := by
    apply Nat.card_congr
    refine
      { toFun := fun y => ⟨⟨y.1 * x⁻¹, y.2.2⟩, ?_⟩
        invFun := fun h => ⟨h.1 * x, ⟨?_, ?_⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · rw [translate_apply_eq_inv_iff hx]
      have : (y.1 * x⁻¹) * x = y.1 := by group
      rw [this]
      exact y.2.1
    · exact (translate_apply_eq_inv_iff hx (h : G)).mp h.2
    · show ((h : G) * x) * x⁻¹ ∈ H
      rw [mul_inv_cancel_right]
      exact h.1.2
    · intro y
      apply Subtype.ext
      simp only [Subtype.coe_mk]
      group
    · intro h
      apply Subtype.ext
      simp only [Subtype.coe_mk]
      group
  rw [heq] at hxcard
  exact hxcard

end CFSG.GroupTheory.SmallFixedTwoGroup
