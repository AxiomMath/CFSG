module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelImage
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelFamily

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionConjugacy

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CatalogueBOrthogonalSmallFamilyOrbit CatalogueBStabilizerFamily
open CatalogueBOrthogonalPointPlusFamilyOrbit CatalogueBOrthogonalPointPlusBorel
open CatalogueBOrthogonalPointReindexCovariance
open CatalogueBOrthogonalSemilinear (matrixProjectiveDerived matrixProjectiveImage)
open CatalogueBOrthogonalPointData (projectivePointFamily projectivePointFamilyAut
  mem_projectivePointFamilyAut_iff coordinateQuadOdd coordinateQuadPlus coordinateQuadMinus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  (orthogonal_geometry_tail_model_point_family_invariant)
open scoped Pointwise

variable {G : Type} [Group G]

theorem mem_image_of_familyAut_eq_top {K : Type} [Field K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (htop : projectivePointFamilyAut Q = ⊤)
    (himage : projectivePointFamilyAut Q = matrixProjectiveImage Q)
    (alpha : MulAut (matrixProjectiveDerived Q)) : alpha ∈ matrixProjectiveImage Q := by
  rw [← himage, htop]
  exact Subgroup.mem_top _

theorem congr_mem_pointFamilyAut {n : ℕ} {K : Type} [Field K]
    (gamma : MulAut (StatedProj (StatedOmega (StatedQuadPlus n K))))
    (hgamma : gamma • statedPointFamily (coe_quadPlus n K) =
      statedPointFamily (coe_quadPlus n K)) :
    MulAut.congr (plusCoordinateEquiv n K) gamma ∈ projectivePointFamilyAut
      (coordinateQuadPlus n K) := by
  rw [mem_projectivePointFamilyAut_iff]
  change MulAut.congr (plusCoordinateEquiv n K) gamma • projectivePointFamily
    (coordinateQuadPlus n K) = projectivePointFamily (coordinateQuadPlus n K)
  rw [← plusCoordinate_pointFamily, ← familyTransport_automorphism, hgamma]

theorem plus_four_conjugacy {K : Type} [Field K] [Finite K] :
    (∀ alpha : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)), alpha * alpha = 1 →
      ∃ beta, beta⁻¹ * alpha * beta ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K)) ∧
    (Nat.card (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
        (projectivePointFamily (coordinateQuadPlus 4 K))) = 1 ∨
      Nat.card (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
        (projectivePointFamily (coordinateQuadPlus 4 K))) = 3) := by
  have hO := stated_pointFamily_orbit_subset (K := K) (n := 4) rfl
  let c := MulAut.congr (plusCoordinateEquiv 4 K)
  refine ⟨fun alpha halpha => ?_, ?_⟩
  · obtain ⟨gamma, rfl⟩ := c.surjective alpha
    have hgamma : gamma * gamma = 1 := by
      apply c.injective
      rw [map_mul, halpha, map_one]
    obtain ⟨beta, hbeta⟩ :=
      CatalogueBOrthogonalPointPlusSwap.exists_conj_smul_statedPointFamily 4 K (by omega) hO gamma
        hgamma
    refine ⟨c beta, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congr_mem_pointFamilyAut _ hbeta
  · have hcard := CatalogueBOrthogonalPointPlusSwap.statedPointFamily_orbit_card 4 K (by omega) hO
    have heq : Nat.card (MulAction.orbit (MulAut (matrixProjectiveDerived
        (coordinateQuadPlus 4 K))) (projectivePointFamily (coordinateQuadPlus 4 K))) =
        Nat.card (MulAction.orbit (MulAut (StatedProj (StatedOmega (StatedQuadPlus 4 K))))
          (statedPointFamily (coe_quadPlus 4 K))) := by
      rw [← plusCoordinate_pointFamily, ← familyTransport_orbit]
      exact Nat.card_image_of_injective (familyTransport _).injective _
    rw [heq]
    exact hcard

@[expose] def InvolutionsConjugateIntoImage (G : Type) [Group G] (t : StatedLieTag)
    (n p f : ℕ) : Prop :=
  match t with
  | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)) →
      ∀ alpha : MulAut (matrixProjectiveDerived (coordinateQuadOdd n K)), alpha * alpha = 1 →
        ∃ beta, beta⁻¹ * alpha * beta ∈ matrixProjectiveImage (coordinateQuadOdd n K)
  | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)) →
      (∀ alpha : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)), alpha * alpha = 1 →
        ∃ beta, beta⁻¹ * alpha * beta ∈ matrixProjectiveImage (coordinateQuadPlus n K)) ∧
      (n = 4 →
        Nat.card (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
            (projectivePointFamily (coordinateQuadPlus n K))) = 1 ∨
          Nat.card (MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))
            (projectivePointFamily (coordinateQuadPlus n K))) = 3)
  | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = p ^ f →
      ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)) →
      ∀ alpha : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)),
        alpha * alpha = 1 →
        ∃ beta, beta⁻¹ * alpha * beta ∈ matrixProjectiveImage (coordinateQuadMinus n K hn b c)
  | _ => False

theorem odd_orthogonal_involutions_conjugate_into_semilinear_image (t : StatedLieTag)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {n p f : ℕ}
    (h : StatedClassicalModel G t n p f) : InvolutionsConjugateIntoImage G t n p f := by
  rcases ht with rfl | rfl | rfl
  · intro K _ _ hK e alpha _
    refine ⟨1, mem_image_of_familyAut_eq_top
      (orthogonal_geometry_tail_model_point_family_invariant G .POmegaOdd (.inl rfl) n p f h K
        hK).2
      (CatalogueBOrthogonalPointData.coordinate_odd_family_eq_matrixImage h K hK e) _⟩
  · intro K _ _ hK e
    have himage := CatalogueBOrthogonalPointData.coordinate_plus_family_eq_matrixImage h K hK e
    have hn : 4 ≤ n := h.1.2.2
    refine ⟨fun alpha halpha => ?_, fun hn4 => ?_⟩
    · rcases Nat.lt_or_ge n 5 with hlt | hge
      · obtain rfl : n = 4 := by omega
        obtain ⟨beta, hbeta⟩ := (plus_four_conjugacy (K := K)).1 alpha halpha
        exact ⟨beta, himage ▸ hbeta⟩
      · exact ⟨1, mem_image_of_familyAut_eq_top (coordinate_plus_pointFamilyAut_eq_top hge)
          himage _⟩
    · subst hn4
      exact (plus_four_conjugacy (K := K)).2
  · intro hn K _ _ hK b c hirr e alpha _
    refine ⟨1, mem_image_of_familyAut_eq_top
      (orthogonal_geometry_tail_model_point_family_invariant G .POmegaMinus (.inr rfl) n p f h
        hn K hK b c hirr).2
      (CatalogueBOrthogonalPointData.coordinate_minus_family_eq_matrixImage h hn K hK b c hirr
        e) _⟩

end CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionConjugacy
