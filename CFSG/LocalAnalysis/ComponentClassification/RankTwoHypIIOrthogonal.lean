module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIOrthogonalLinear
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIOrthogonalFree
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataPlusImage
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalInvolutionConjugacy
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenOrthogonalComponents
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.ComponentClassification.RankTwoHypIIOrthogonal

open Subgroup CFSG.Open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoHypIIY CFSG.ComponentClassification.RankTwoHypIIClassical
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ClassicalGroups.Orthogonal (elementaryGroup)
open scoped Pointwise

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] in
theorem center_PQ_eq_bot {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) :
    center (matrixProjectiveDerived Q) = ⊥ := by
  have hcinj :=
    UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived hQ hT hE
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  apply hcinj
  rw [map_one]
  ext y
  rw [MulAut.conj_apply, MulAut.one_apply, (mem_center_iff.mp hx y).symm, mul_inv_cancel_right]

theorem hypII_of_regular {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)}
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ E : Subgroup (MulAut (matrixProjectiveDerived Q)), IsPGroup 2 E →
      ∃ β : MulAut (matrixProjectiveDerived Q),
        E.map (MulAut.conj β⁻¹).toMonoidHom ≤ matrixProjectiveImage Q)
    {A : Type} [Group A] (hA : commutator A = ⊤) (hodd : Odd (Nat.card (center A)))
    (e : A ⧸ center A ≃* matrixProjectiveDerived Q) : AS76b.HypII A := by
  have := finite_mulAut_PQ (Q := Q)
  refine hypII_of_forall_not_config (autModel_mulAut (center_PQ_eq_bot hQ hT hE))
    (fun E M h => ?_) hA hodd e
  have h' : HypIIConfig (inner (matrixProjectiveDerived Q)) E M := h
  obtain ⟨β, hβ⟩ := hconj E fun x => ⟨1, Subtype.ext (by simpa using h'.elemAbelian.2 x x.2)⟩
  exact false_of_linear hQ hT hE orthLinearConfigFree hf hK hn
    (h'.conj (OuterAutomorphisms.inner_normal _) β⁻¹) hβ

omit [CharP K 2] in
theorem exists_conj_le_image_plus_four {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (E : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))))
    (hE2 : IsPGroup 2 E) :
    ∃ β : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K)),
      E.map (MulAut.conj β⁻¹).toMonoidHom ≤ matrixProjectiveImage (coordinateQuadPlus 4 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_mulAut_PQ (Q := coordinateQuadPlus 4 K)
  set F := projectivePointFamily (coordinateQuadPlus 4 K) with hF
  set O := MulAction.orbit (MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 K))) F
  have hcard : Nat.card O = 1 ∨ Nat.card O = 3 :=
    (CatalogueBOrthogonalInvolutionConjugacy.plus_four_conjugacy (K := K)).2
  have hodd : ¬ 2 ∣ Nat.card O := by
    rcases hcard with h | h <;> rw [h] <;> decide
  obtain ⟨⟨F', ⟨β, hβ⟩⟩, hfix⟩ := hE2.nonempty_fixed_point_of_prime_not_dvd_card O hodd
  change β • F = F' at hβ
  refine ⟨β, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  have hfe := congrArg Subtype.val (hfix ⟨e, he⟩)
  change e • F' = F' at hfe
  have hmod : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus 4 K)))
      .POmegaPlus 4 2 f :=
    ⟨⟨Nat.prime_two, hf, le_rfl⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  rw [← coordinate_plus_family_eq_matrixImage hmod K hK (MulEquiv.refl _)]
  change (MulAut.conj β⁻¹) e • F = F
  rw [MulAut.conj_apply, inv_inv, mul_smul, mul_smul]
  change β⁻¹ • e • β • F = F
  rw [hβ, hfe, ← hβ, inv_smul_smul]

theorem hypII_of_pomegaPlus {A : Type} [Group A] (hA : commutator A = ⊤)
    (hodd : Odd (Nat.card (center A))) {n m : ℕ} (hn : 4 ≤ n)
    (h : StatedClassicalModel (A ⧸ center A) .POmegaPlus n 2 m) : AS76b.HypII A := by
  obtain ⟨⟨-, hm, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hm hK
  have hreg := regular_coordinateQuadPlus n K (by omega)
  refine hypII_of_regular hm hK hn hreg.1 hreg.2 (commutator_coordinateQuadPlus n K (by omega))
    (fun E hE2 => ?_) hA hodd (coordinatePlusWitnessEquiv K e)
  rcases Nat.lt_or_ge n 5 with h4 | h5
  · obtain rfl : n = 4 := by omega
    exact exists_conj_le_image_plus_four hm hK E hE2
  · refine ⟨1, ?_⟩
    rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n h5]
    exact le_top

theorem hypII_of_pomegaMinus {A : Type} [Group A] (hA : commutator A = ⊤)
    (hodd : Odd (Nat.card (center A))) {n m : ℕ} (hn : 4 ≤ n)
    (h : StatedClassicalModel (A ⧸ center A) .POmegaMinus n 2 m) : AS76b.HypII A := by
  obtain ⟨⟨-, hm, -⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hm hK
  have hreg := regular_coordinateQuadMinus n K b c hn hirr
  refine hypII_of_regular hm hK hn hreg.1 hreg.2 (commutator_coordinateQuadMinus n K b c hn hirr)
    (fun E _ => ⟨1, ?_⟩) hA hodd (coordinateMinusWitnessEquiv K (by omega) b c e)
  rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c hirr]
  exact le_top

theorem orthogonalHypIIOdd : RankTwoClassical.OrthogonalHypIIOdd := by
  intro A _ _ hA hodd n m hn h
  rcases h with h | h
  · exact hypII_of_pomegaPlus hA hodd hn h
  · exact hypII_of_pomegaMinus hA hodd hn h

end CFSG.ComponentClassification.RankTwoHypIIOrthogonal
