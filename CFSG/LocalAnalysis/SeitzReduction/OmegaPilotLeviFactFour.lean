module

public import CFSG.Quasithin.Background.P3OrthoOm4
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataSemilinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataQuotient
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactBlock

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbedGL)
open CFSG.SeitzReduction.SymplecticPilot (suppGL planeCoords planeEnum planeEnum_injective
  range_planeEnum range_sumMap_eq_planeCoords planeTorusParam liftParam)

variable {F : Type} [Field F] {m : ℕ}

theorem commutator_statedOmega_quadPlus_two [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F) :
    ⁅StatedOmega (StatedQuadPlus 2 F), StatedOmega (StatedQuadPlus 2 F)⁆ =
      StatedOmega (StatedQuadPlus 2 F) := by
  obtain ⟨e⟩ := CFSG.Quasithin.G11.P3Ortho.Om4.iso_of_card F hF
  have hSL := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F hF
  have : Group.IsPerfect
      (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.Quasithin.G11.P3Ortho.Om4.isPerfect_prod hSL hSL
  have hΩ : Group.IsPerfect (StatedOmega (StatedQuadPlus 2 F)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.isPerfect_iff.1 hΩ

theorem commutator_statedOmega_quadPlus_of_two_le [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    {k : ℕ} (hk : 2 ≤ k) :
    ⁅StatedOmega (StatedQuadPlus k F), StatedOmega (StatedQuadPlus k F)⁆ =
      StatedOmega (StatedQuadPlus k F) := by
  rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | hk3
  · exact commutator_statedOmega_quadPlus_two hF
  · exact Subgroup.isPerfect_iff.1
      (CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadPlus (K := F) hk3)

theorem perfectCore_omegaBlock_of_two_le [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F)
    {N : Finset (Fin m)} (hN : 2 ≤ N.card) :
    perfectCore (omegaBlock F N) =
      (StatedOmega (StatedQuadPlus N.card F)).map
        (spEmbedGL (planeEnum N) (planeEnum_injective N)) := by
  have h := perfectCore_statedOmega_inf_suppGL (F := F) (planeEnum_injective N)
    (commutator_statedOmega_quadPlus_of_two_le hF hN)
  rwa [range_sumMap_eq_planeCoords (range_planeEnum N)] at h

theorem perfectCore_statedOmega_inf_centralizer_eq_map_of_two_le [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) {I : Finset (Fin m)} (hI : 2 ≤ I.card) (D : Set (Fin m → Fˣ))
    (hconst : ∀ s ∈ D, ∀ a ∈ planeCoords I, ∀ b ∈ planeCoords I,
      SymplecticPilot.diagSpEntry s a = SymplecticPilot.diagSpEntry s b)
    (hsep : ∀ a b : Fin m ⊕ Fin m, a ≠ b → (a ∉ planeCoords I ∨ b ∉ planeCoords I) →
      ∃ s ∈ D, SymplecticPilot.diagSpEntry s a ≠ SymplecticPilot.diagSpEntry s b) :
    perfectCore (StatedOmega (StatedQuadPlus m F) ⊓ centralizer (diagOmega F m '' D)) =
      (StatedOmega (StatedQuadPlus I.card F)).map
        (spEmbedGL (planeEnum I) (planeEnum_injective I)) := by
  rw [perfectCore_statedOmega_inf_centralizer_eq_perfectCore_omegaBlock D hconst hsep,
    perfectCore_omegaBlock_of_two_le hF hI]

theorem nonempty_perfectCore_omegaBlock_mulEquiv_SL2 [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) {I : Finset (Fin m)} (hI : I.card = 2) :
    Nonempty (perfectCore (omegaBlock F I) ≃*
      (Matrix.SpecialLinearGroup (Fin 2) F × Matrix.SpecialLinearGroup (Fin 2) F)) := by
  obtain ⟨e⟩ := CFSG.Quasithin.G11.P3Ortho.Om4.iso_of_card F hF
  have h := perfectCore_omegaBlock_of_two_le hF (N := I) (by omega)
  have e1 : perfectCore (omegaBlock F I) ≃* StatedOmega (StatedQuadPlus I.card F) :=
    (MulEquiv.subgroupCongr h).trans
      ((StatedOmega (StatedQuadPlus I.card F)).equivMapOfInjective _
        (spEmbedGL_injective (planeEnum_injective I))).symm
  have e2 : StatedOmega (StatedQuadPlus I.card F) ≃* StatedOmega (StatedQuadPlus 2 F) := by
    rw [hI]
  exact ⟨(e1.trans e2).trans e⟩

end CFSG.SeitzReduction.OmegaPilot
