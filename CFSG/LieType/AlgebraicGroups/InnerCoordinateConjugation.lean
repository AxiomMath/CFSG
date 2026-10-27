module
public import CFSG.LieType.AlgebraicGroups.ClosedSubgroupInnerCoordinate
public import CFSG.LieType.AlgebraicGroups.CoordinateConjugation

public noncomputable section
namespace CFSG.LieType.AlgebraicGroups
open WithConv Subgroup CategoryTheory
open scoped CFSG.ConvolutionPoints

variable {k : Type} [Field k] [IsAlgClosed k]
 {A : Type} [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A]

theorem innerCoordinate_eq_pointConjugation
    (H : Subgroup (WithConv (A →ₐ[k] k)))
    (hH : pointsZero k (subgroupIdeal H) = subgroupPoints H)
    (a : WithConv (A →ₐ[k] k)) (ha : a ∈ H)
    (hn : ∀ y ∈ H, a * y * a⁻¹ ∈ H) :
    innerCoordinate H a hn =
      (TauCeti.HopfAlgebra.pointConjugationBialgEquiv
        ((subgroupQuotientPointsEquiv H hH).symm ⟨a, ha⟩)).toBialgHom := by
  have : IsReduced (A ⧸ subgroupIdeal H) := (Ideal.isRadical_iff_quotient_reduced _).1
    (isRadical_pointsIdeal _)
  let e := subgroupQuotientPointsEquiv H hH
  let ap := e.symm ⟨a,ha⟩
  let σ := (TauCeti.HopfAlgebra.pointConjugationBialgEquiv ap).toBialgHom
  apply BialgHom.ext
  intro q
  rw [← sub_eq_zero]
  apply eq_zero_of_forall_algHom k (A ⧸ subgroupIdeal H)
  intro y
  rw [map_sub, sub_eq_zero]
  have hσ : toConv (y.comp σ.toAlgHom) = ap * toConv y * ap⁻¹ := by
    rw [show σ.toAlgHom = innerCo ap from pointConjugationBialgEquiv_toAlgHom_eq_innerCo ap]
    exact point_comp_innerCo _ ap
  have hi := innerCoordinate_on_points H a hn (toConv y)
  have hp := congrArg (fun x : H => (x : WithConv (A →ₐ[k] k)))
    (e.apply_symm_apply ⟨a,ha⟩)
  have hip : e (toConv (y.comp (innerCoordinate H a hn).toAlgHom)) =
      e (toConv (y.comp σ.toAlgHom)) := by
    apply Subtype.ext
    rw [hσ, map_mul, map_mul, map_inv, e.apply_symm_apply]
    change toConv ((y.comp (innerCoordinate H a hn).toAlgHom).comp
      (Ideal.Quotient.mkₐ k _)) =
      a * toConv (y.comp (Ideal.Quotient.mkₐ k _)) * a⁻¹
    exact congrArg toConv hi
  have hi' := e.injective hip
  have h := congrArg (fun x : WithConv ((A ⧸ subgroupIdeal H) →ₐ[k] k) => x.ofConv q) hi'
  exact h

end CFSG.LieType.AlgebraicGroups
