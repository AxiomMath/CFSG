module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

open scoped commutatorElement

namespace CFSG.OddStandard.SmallF3.Omega

theorem fg_oz_comm_inv {E : Type*} [Group E] {w u v z₁ z₂ : E}
    (hcv : Commute ⁅u, v⁆ v) (hz₁u : Commute z₁ u) (hz₁v : Commute z₁ v)
    (hz₁z₂ : Commute z₁ z₂) (hz₂u : Commute z₂ u) (hz₂v : Commute z₂ v)
    (hu : w * u * w⁻¹ = u * z₁) (hv : w * v * w⁻¹ = v⁻¹ * z₂) :
    w * ⁅u, v⁆ * w⁻¹ = ⁅u, v⁆⁻¹ := by
  have hz₁ : ⁅z₁, v⁻¹ * z₂⁆ = 1 := (hz₁v.inv_right.mul_right hz₁z₂).commutator_eq
  have hz₂ : ⁅u, z₂⁆ = 1 := hz₂u.symm.commutator_eq
  have hc : ⁅u, v⁻¹⁆ = ⁅u, v⁆⁻¹ := by
    rw [commutatorElement_inv_right, (commutatorElement_inv u v).symm, mul_assoc,
      hcv.inv_left.eq]
    group
  calc
    w * ⁅u, v⁆ * w⁻¹ = ⁅u * z₁, v⁻¹ * z₂⁆ := by
      rw [conjugate_commutatorElement, hu, hv]
    _ = ⁅u, v⁻¹ * z₂⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hz₁]
      group
    _ = ⁅u, v⁻¹⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hz₂]
      group
    _ = ⁅u, v⁆⁻¹ := hc

end CFSG.OddStandard.SmallF3.Omega
