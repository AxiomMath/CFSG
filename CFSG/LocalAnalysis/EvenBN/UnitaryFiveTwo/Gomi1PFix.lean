module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpDescent
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusSp4Main
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
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
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpInner
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec6.BThreeCensus

@[expose] def frobSp (K : Type) [Field K] (Fr : K ≃+* K) : StatedSp 2 K →* StatedSp 2 K :=
  (fieldSp 2 K Fr).toMonoidHom

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem frobenius_facts_four (hK : Nat.card K = 4) {Fr : K ≃+* K} (hFr : ∀ x, Fr x = x ^ 2) :
    Fr * Fr = 1 ∧ Fr ≠ 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  have h4 : ∀ x : K, x ^ 4 = x := fun x => by
    have := FiniteField.pow_card x
    rwa [hcard] at this
  refine ⟨?_, ?_⟩
  · ext x
    rw [RingAut.mul_apply, hFr, hFr, ← pow_mul, show 2 * 2 = 4 from rfl, h4]
    rfl
  · intro h
    have hsq : ∀ x : K, x ^ 2 = x := fun x => by rw [← hFr, h]; rfl
    have hroots : (Finset.univ : Finset K) ⊆ (Polynomial.roots (Polynomial.X ^ 2 - Polynomial.X :
        Polynomial K)).toFinset := by
      intro x _
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (by
        intro hz
        have := congrArg (Polynomial.coeff · 2) hz
        simp [Polynomial.coeff_X_pow, Polynomial.coeff_X_of_ne_one (by norm_num : (2 : ℕ) ≠ 1)]
          at this)]
      simp [sub_eq_zero, hsq x]
    have hle := Finset.card_le_card hroots
    have hdeg : (Polynomial.roots (Polynomial.X ^ 2 - Polynomial.X : Polynomial K)).toFinset.card
        ≤ 2 := by
      refine (Multiset.toFinset_card_le _).trans ?_
      refine (Polynomial.card_roots' _).trans ?_
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simp)]
      simp
    rw [Finset.card_univ, hcard] at hle
    omega

theorem eqLocus_fieldSp_eq_range {Fr : K ≃+* K} :
    (frobSp K Fr).eqLocus (MonoidHom.id (StatedSp 2 K)) =
      (subfieldSpHom 2 (descentField Fr)).range := by
  ext g
  constructor
  · intro hg
    exact exists_subfieldSpHom_eq (σ := Fr) hg
  · rintro ⟨g₀, rfl⟩
    exact fieldSp_subfieldSpHom (σ := Fr) g₀

theorem card_fixedField_four (hK : Nat.card K = 4) {Fr : K ≃+* K} (hFr : ∀ x, Fr x = x ^ 2) :
    Nat.card (descentField Fr) = 2 := by
  obtain ⟨h1, h2⟩ := frobenius_facts_four hK hFr
  have := (ringEquiv_involution_facts (f := 2) (by norm_num) (by rw [hK]; norm_num) h1 h2).2.2
  simpa using this

theorem card_eqLocus_fieldSp (hK : Nat.card K = 4) {Fr : K ≃+* K} (hFr : ∀ x, Fr x = x ^ 2) :
    Nat.card ((frobSp K Fr).eqLocus (MonoidHom.id (StatedSp 2 K))) = 720 := by
  rw [eqLocus_fieldSp_eq_range]
  have hk2 : Nat.card (descentField Fr) = 2 := card_fixedField_four hK hFr
  have : CharP (descentField Fr) 2 := inferInstance
  have h := Nat.card_congr (MonoidHom.ofInjective (subfieldSpHom_injective (r := 2)
    (descentField Fr))).toEquiv
  rw [← h]
  exact card_statedSp_two_of_card_two hk2

theorem center_eqLocus_fieldSp {Fr : K ≃+* K} :
    ∀ a ∈ (frobSp K Fr).eqLocus (MonoidHom.id (StatedSp 2 K)),
      (∀ b ∈ (frobSp K Fr).eqLocus (MonoidHom.id (StatedSp 2 K)), a * b = b * a) → a = 1 := by
  intro a ha hc
  rw [eqLocus_fieldSp_eq_range] at ha hc
  obtain ⟨a₀, rfl⟩ := ha
  have hz : a₀ ∈ Subgroup.center (StatedSp 2 (descentField Fr)) := by
    rw [Subgroup.mem_center_iff]
    intro b₀
    apply subfieldSpHom_injective (r := 2) (descentField Fr)
    rw [map_mul, map_mul]
    exact (hc _ ⟨b₀, rfl⟩).symm
  rw [center_statedSp_two_eq_bot, Subgroup.mem_bot] at hz
  rw [hz, map_one]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
