module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalInvolutionConjugacy

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixProjectiveDerived matrixProjectiveImage)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus)
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionConjugacy
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  (orthogonal_geometry_tail_model_point_family_invariant)

namespace OmegaRadical

@[expose] def SemilinearImageEqTop (G : Type) [Group G] (t : StatedLieTag) (n p f : ℕ) : Prop :=
  match t with
  | .POmegaPlus => 5 ≤ n → ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)) →
        matrixProjectiveImage (coordinateQuadPlus n K) = ⊤
  | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)) →
        matrixProjectiveImage (coordinateQuadMinus n K hn b c) = ⊤
  | _ => False

theorem semilinearImageEqTop (G : Type) [Group G] (t : StatedLieTag)
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {n p f : ℕ}
    (h : StatedClassicalModel G t n p f) : SemilinearImageEqTop G t n p f := by
  rcases ht with rfl | rfl
  · intro h5 K _ _ hK e
    rw [← CatalogueBOrthogonalPointData.coordinate_plus_family_eq_matrixImage h K hK e]
    exact CatalogueBOrthogonalPointPlusFamilyOrbit.coordinate_plus_pointFamilyAut_eq_top h5
  · intro hn K _ _ hK b c hirr e
    rw [← CatalogueBOrthogonalPointData.coordinate_minus_family_eq_matrixImage h hn K hK b c
      hirr e]
    exact (orthogonal_geometry_tail_model_point_family_invariant G .POmegaMinus (.inr rfl) n p f
      h hn K hK b c hirr).2

end OmegaRadical

open OmegaRadical in
theorem even_orthogonal_involutions_conjugate_into_semilinear_image (G : Type) [Group G]
    (t : StatedLieTag) (ht : t = .POmegaPlus ∨ t = .POmegaMinus) (n f : ℕ)
    (h : StatedClassicalModel G t n 2 f) :
    InvolutionsConjugateIntoImage G t n 2 f ∧ SemilinearImageEqTop G t n 2 f :=
  ⟨odd_orthogonal_involutions_conjugate_into_semilinear_image t (.inr ht) h,
    semilinearImageEqTop G t ht h⟩

end CFSG.ComponentClassification.UnbalancedCatalog
