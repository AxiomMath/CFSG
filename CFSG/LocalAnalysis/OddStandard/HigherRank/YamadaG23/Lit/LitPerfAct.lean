module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

theorem lit_perfect_central_action {X : Type*} [Group X] (τ : X ≃* X) {H : Subgroup X}
    (hH : ⁅H, H⁆ = H) (hmem : ∀ x ∈ H, τ x * x⁻¹ ∈ H)
    (hcent : ∀ x ∈ H, ∀ y ∈ H, (τ x * x⁻¹) * y = y * (τ x * x⁻¹)) : ∀ x ∈ H, τ x = x := by
  let φ : H →* X :=
    { toFun := fun x => τ (x : X) * (x : X)⁻¹
      map_one' := by simp
      map_mul' := by
        intro x y
        have hc : Commute (τ (y : X) * (y : X)⁻¹) (x : X) := hcent y y.2 x x.2
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        rw [show τ (x : X) * τ (y : X) * ((y : X)⁻¹ * (x : X)⁻¹) =
              τ (x : X) * ((τ (y : X) * (y : X)⁻¹) * (x : X)⁻¹) by group,
            hc.inv_right.eq,
            show τ (x : X) * ((x : X)⁻¹ * (τ (y : X) * (y : X)⁻¹)) =
              (τ (x : X) * (x : X)⁻¹) * (τ (y : X) * (y : X)⁻¹) by group] }
  have key : ∀ a ∈ H, ∀ b ∈ H, τ ⁅a, b⁆ = ⁅a, b⁆ := by
    intro a ha b hb
    let A : H := ⟨a, ha⟩
    let B : H := ⟨b, hb⟩
    have hker : φ ⁅A, B⁆ = 1 := by
      rw [map_commutatorElement (f := φ)]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hcent a ha (τ b * b⁻¹) (hmem b hb))
    exact mul_inv_eq_one.mp hker
  let K : Subgroup X :=
    { carrier := {x : X | τ x = x}
      one_mem' := by
        show τ 1 = 1
        exact map_one τ
      mul_mem' := by
        intro x y hx hy
        show τ (x * y) = x * y
        rw [map_mul, hx, hy]
      inv_mem' := by
        intro x hx
        show τ x⁻¹ = x⁻¹
        rw [map_inv, hx] }
  have hle : ⁅H, H⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact key a ha b hb
  intro x hx
  exact hle (hH.symm ▸ hx)

end CFSG.OddStandard.HigherRank.YamadaG23
