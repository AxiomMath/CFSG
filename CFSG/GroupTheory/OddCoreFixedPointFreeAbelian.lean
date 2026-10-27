module

public import Mathlib.GroupTheory.FixedPointFree
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG

theorem oddCore_commute_of_fixedPointFree_involution {X : Type*} [Group X] [Finite X]
    {τ : X} (hτ2 : τ * τ = 1)
    (hfree : ∀ y : X, y ∈ oddCore X → τ * y * τ⁻¹ = y → y = 1) :
    ∀ a ∈ oddCore X, ∀ b ∈ oddCore X, a * b = b * a := by
  let Y : Subgroup X := oddCore X
  have hYnorm : Y.Normal := oddCore_normal X
  let φ : Y →* Y :=
    { toFun := fun y => ⟨τ * (y : X) * τ⁻¹, hYnorm.conj_mem (y : X) y.2 τ⟩
      map_one' := by
        ext
        simp
      map_mul' := fun y z => by
        ext
        simp only [Subgroup.coe_mul, Subtype.coe_mk]
        group }
  have hφfree : MonoidHom.FixedPointFree φ := by
    intro y hy
    apply Subtype.ext
    have hco : τ * (y : X) * τ⁻¹ = (y : X) :=
      congrArg (fun z : Y => (z : X)) hy
    exact hfree (y : X) y.2 hco
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_left hτ2
  have hφinv : Function.Involutive φ := by
    intro y
    apply Subtype.ext
    calc
      τ * (τ * (y : X) * τ⁻¹) * τ⁻¹ = (τ * τ) * (y : X) * (τ⁻¹ * τ⁻¹) := by group
      _ = (y : X) := by simp [hτ2, hτinv]
  intro a ha b hb
  have hcomm := MonoidHom.FixedPointFree.commute_all_of_involutive hφfree hφinv
    ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg (fun z : Y => (z : X)) hcomm.eq

end CFSG
