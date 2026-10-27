module

public import CFSG.ThirdParty.Mathlib.SmoothGroupAlgClosed
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.RingHom.Smooth

public section

open CategoryTheory

namespace CFSG.LieType.AlgebraicGroups

open AlgebraicGeometry

universe u

theorem smooth_of_hopfAlgebra_of_isReduced (k : Type u) [Field k] [IsAlgClosed k] (R : Type u)
    [CommRing R] [HopfAlgebra k R] [Algebra.FiniteType k R] [IsReduced R] :
    Algebra.Smooth k R ∧ Smooth (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k)) := by
  let : HopfAlgebra (CommRingCat.of k) (CommRingCat.of R) := inferInstanceAs (HopfAlgebra k R)
  let : GrpObj (Over.mk (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k))) :=
    (inferInstance : GrpObj ((Spec (CommRingCat.of R)).asOver (Spec (CommRingCat.of k))))
  have : Algebra.FiniteType (CommRingCat.of k) (CommRingCat.of R) :=
    inferInstanceAs (Algebra.FiniteType k R)
  have h1 : Smooth (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k)) :=
    CFSG.ThirdParty.Mathlib.smooth_of_grpObj_of_isReduced_of_isAlgClosed (K := k) _
  refine ⟨?_, h1⟩
  rw [specOverSpec_over, HasRingHomProperty.Spec_iff (P := @Smooth)] at h1
  exact RingHom.smooth_algebraMap.1 h1

theorem exceptional_Lang_reduced_affine_group_smooth (k : Type u) [Field k] [IsAlgClosed k] :
    (∀ (R : Type u) [CommRing R] [HopfAlgebra k R] [Algebra.FiniteType k R] [IsReduced R],
      Algebra.Smooth k R ∧ Smooth (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of k))) ∧
    ∀ {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
      [GrpObj (Over.mk f)] [IsReduced G], Smooth f :=
  ⟨fun R _ _ _ _ => smooth_of_hopfAlgebra_of_isReduced k R,
    fun f _ _ _ => CFSG.ThirdParty.Mathlib.smooth_of_grpObj_of_isReduced_of_isAlgClosed f⟩

end CFSG.LieType.AlgebraicGroups
