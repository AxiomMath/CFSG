module

public import Mathlib.GroupTheory.IsPerfect

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction

universe u

variable {G : Type u} [Group G]

theorem central_quotient_discrepancy_mem (R : Subgroup G) [R.Normal]
    (f : G →* G) (hf : ∀ x : G, QuotientGroup.mk' R (f x) = QuotientGroup.mk' R x)
    (x : G) : f x * x⁻¹ ∈ R := by
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' R (f x * x⁻¹) = 1
  rw [map_mul, map_inv, hf, mul_inv_cancel]

@[expose] def centralQuotientDiscrepancy (R : Subgroup G) [R.Normal]
    (hcentral : R ≤ Subgroup.center G) (f : G →* G)
    (hf : ∀ x : G, QuotientGroup.mk' R (f x) = QuotientGroup.mk' R x) : G →* R where
  toFun x := ⟨f x * x⁻¹, central_quotient_discrepancy_mem R f hf x⟩
  map_one' := by
    apply Subtype.ext
    simp only [map_one, inv_one, mul_one, Subgroup.coe_one]
  map_mul' x y := by
    apply Subtype.ext
    change f (x * y) * (x * y)⁻¹ = (f x * x⁻¹) * (f y * y⁻¹)
    have hcomm : (f y * y⁻¹) * x⁻¹ = x⁻¹ * (f y * y⁻¹) :=
      (hcentral (central_quotient_discrepancy_mem R f hf y)).comm _
    rw [map_mul, mul_inv_rev]
    calc
      f x * f y * (y⁻¹ * x⁻¹) = f x * ((f y * y⁻¹) * x⁻¹) := by
        simp only [mul_assoc]
      _ = f x * (x⁻¹ * (f y * y⁻¹)) := by rw [hcomm]
      _ = (f x * x⁻¹) * (f y * y⁻¹) := by simp only [mul_assoc]

theorem central_quotient_trivial_hom_eq_id [Group.IsPerfect G]
    (R : Subgroup G) [R.Normal] (hcentral : R ≤ Subgroup.center G)
    (f : G →* G) (hf : ∀ x : G, QuotientGroup.mk' R (f x) = QuotientGroup.mk' R x) :
    f = MonoidHom.id G := by
  let d := centralQuotientDiscrepancy R hcentral f hf
  let dc : G →* Subgroup.center G := (Subgroup.inclusion hcentral).comp d
  have hker : commutator G ≤ dc.ker := Abelianization.commutator_subset_ker dc
  apply MonoidHom.ext
  intro x
  have hx := MonoidHom.mem_ker.mp (hker (Group.IsPerfect.mem_commutator (g := x)))
  have hdiscrepancy : f x * x⁻¹ = 1 := congrArg Subtype.val hx
  exact mul_inv_eq_one.mp hdiscrepancy

end CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction
