module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing

public section

open CategoryTheory WithConv TauCeti
open scoped commutatorElement

namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k]

theorem quotientPointsSubgroup_vanishingIdeal_centralizer
    (H : FiniteTypeCommHopfAlgCat.{u,u} k)
    (L : Subgroup (WithConv (H →ₐ[k] k))) :
    CommHopfAlgCat.quotientPointsSubgroup H.obj
      (HopfIdeal.vanishingIdeal (Subgroup.centralizer (L : Set (WithConv (H →ₐ[k] k)))))
      (CommAlgCat.of k k) = Subgroup.centralizer (L : Set (WithConv (H →ₐ[k] k))) := by
  let C := Subgroup.centralizer (L : Set (WithConv (H →ₐ[k] k)))
  let CL := CommHopfAlgCat.quotientPointsSubgroup H.obj
    (HopfIdeal.vanishingIdeal L) (CommAlgCat.of k k)
  let CC := CommHopfAlgCat.quotientPointsSubgroup H.obj
    (HopfIdeal.vanishingIdeal C) (CommAlgCat.of k k)
  have hL : L ≤ CL :=
    (HopfIdeal.le_vanishingIdeal_iff L (HopfIdeal.vanishingIdeal L)).mp le_rfl
  have hC : C ≤ CC :=
    (HopfIdeal.le_vanishingIdeal_iff C (HopfIdeal.vanishingIdeal C)).mp le_rfl
  have hcomm : ⁅C, L⁆ = ⊥ := by
    apply bot_unique
    rw [Subgroup.commutator_le]
    intro c hc l hl
    have h := (Subgroup.mem_centralizer_iff.mp hc) l hl
    change c * l * c⁻¹ * l⁻¹ ∈ (⊥ : Subgroup (WithConv (H →ₐ[k] k)))
    rw [Subgroup.mem_bot]
    calc
      c * l * c⁻¹ * l⁻¹ = l * c * c⁻¹ * l⁻¹ := by rw [h.symm]
      _ = 1 := by group
  have hclosed : ⁅CC, CL⁆ ≤ (⊥ : Subgroup (WithConv (H →ₐ[k] k))) := by
    have h := HopfIdeal.commutator_quotientPointsSubgroup_vanishingIdeal_le C L
    rw [hcomm, HopfIdeal.quotientPointsSubgroup_vanishingIdeal_bot] at h
    exact h
  apply le_antisymm
  · intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hz := hclosed (Subgroup.commutator_mem_commutator hc (hL hl))
    rw [Subgroup.mem_bot] at hz
    have hcl : c * l * c⁻¹ * l⁻¹ = 1 := hz
    calc
      l * c = (c * l * c⁻¹ * l⁻¹) * (l * c) := by rw [hcl, one_mul]
      _ = c * l := by group
  · exact hC

end CFSG.LieType.AlgebraicGroups
