module

public import CFSG.Open.StatedDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04D4FCore
import CFSG.HardMathSupport.Timmesfeld.DFour.Tower
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
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
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.SignLines
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.HardMathSupport.Timmesfeld.DFour
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldAutT coordinateQuadPlus_fieldAut)

theorem exists_inner_or_fieldAutT_d4 {S : Type} [Group S] [Finite S] {r f : ℕ}
    (hm : StatedClassicalModel S .POmegaPlus 4 r f) {A : Subgroup (MulAut S)}
    (hA : ∀ α ∈ A, α ^ 3 = 1) (hA9 : Nat.card A = 9) :
    (∃ α ∈ A, α ≠ 1 ∧ α ∈ (MulAut.conj : S →* MulAut S).range) ∨
      (3 ∣ f ∧ ∃ α ∈ A, α ≠ 1 ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K)
        (ψ : S ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) (σ : K ≃+* K),
        Nat.card K = r ^ f ∧ orderOf σ = 3 ∧
          MulAut.congr ψ α =
            fieldAutT (coordinateQuadPlus 4 K) σ (coordinateQuadPlus_fieldAut 4 σ)) := by
  refine or_iff_not_imp_left.2 fun hinn => ?_
  have hA9' : Nat.card A = 3 ^ 2 := by rw [hA9]; norm_num
  have hAe : IsElemAbelian 3 A := ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hA9', hA⟩
  have hbot : A ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner S = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxI⟩
    rw [Subgroup.mem_bot]
    by_contra hx1
    exact hinn ⟨x, hxA, hx1, hxI⟩
  have hf3 : 3 ∣ f := by
    by_contra hf
    obtain ⟨x, ⟨hxA, hxI⟩, hx1⟩ := meets_inner_of_three_not_dvd hm hf A hAe hA9'
    exact hinn ⟨x, hxA, hx1, hxI⟩
  have h0 := hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  obtain ⟨hQ, hab, hidx⟩ := coordinate_facts_four hm K hK e
  obtain ⟨y, hyA, hy1, hyE, hyD', hyord⟩ :=
    exists_outside_linear K (coordinatePlusWitnessEquiv K e) hQ hab hidx A hAe hA9' hbot
  obtain ⟨-, hrest⟩ :=
    CFSG.HardMathSupport.Lang.Proving.orthogonal_prime_semilinear_actual_fixed_form_descent'
      S .POmegaPlus (Or.inr (Or.inl rfl)) 4 r f 3 hm Nat.prime_three (by norm_num) K hK e
      (MulAut.congr (coordinatePlusWitnessEquiv K e) y) hyE hyD' hyord
  obtain ⟨g, hg⟩ := hyE
  obtain ⟨hord', -, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hg, rfl⟩
  obtain ⟨ν, S₀, -, -, hT⟩ := hDisp
  obtain ⟨S', ν', -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT
  refine ⟨hf3, y, hyA, hy1, K, inferInstance, inferInstance,
    (coordinatePlusWitnessEquiv K e).trans Θ, U.val.right, hK, by rw [hUr]; exact hord', ?_⟩
  exact d4_congr_eq_fieldAutT (coordinatePlusWitnessEquiv K e) Θ y U hUκ g' hg'l hg'r hΘ
    (coordinateQuadPlus_fieldAut 4 U.val.right)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35
