module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

public section

namespace CFSG.GroupTheory

theorem sup_zpowers_le_normalizer_of_inverting {G : Type*} [Group G] {U : Subgroup G} {w : G}
    (hU : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) (hw : w * w = 1)
    (hinv : ∀ u ∈ U, w * u * w⁻¹ = u⁻¹) {P : Subgroup G} (hPU : P ≤ U) :
    U ⊔ Subgroup.zpowers w ≤ Subgroup.normalizer (P : Set G) := by
  refine sup_le ?_ ?_
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer (P : Set G))
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hU x hx y (hPU hy)).symm
  · rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hinv x (hPU hx)]
      exact P.inv_mem hx
    · intro hx
      have h2 := hinv (w * x * w⁻¹) (hPU hx)
      have h3 : w * (w * x * w⁻¹) * w⁻¹ = x := by
        rw [show w * (w * x * w⁻¹) * w⁻¹ = (w * w) * x * (w * w)⁻¹ by group, hw, inv_one,
          one_mul, mul_one]
      rw [h3] at h2
      rw [h2]
      exact P.inv_mem hx

end CFSG.GroupTheory
