module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUPSL
public import CFSG.LocalAnalysis.OddStandard.HigherRank.LinUnit.LUPSU
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSU
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorReduction
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.ClassicalGroups
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpField
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinUInner
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddE6
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocle
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLAllInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveEigenspaceComponent
public import CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonalLocalComponentSplit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.BruhatLift
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SLTwo
public import CFSG.LocalAnalysis.SectionRank.LargeReeCover
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public noncomputable section

namespace CFSG.OddStandard.HigherRank.LinUnit

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatLeafProof.X10Lin (ModelIn modelIn_of_component_equiv)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

@[expose] def luFixedEquiv {K C' : Type} [Group K] [Group C'] (e : K ≃* C') (α : MulAut K) :
    fixedSubgroup α ≃* fixedSubgroup (MulAut.congr e α) :=
  ((fixedSubgroup α).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (ExcSelector.fixedSubgroup_congr e α).symm)

theorem lu_congr_conj {J J' : Type} [Group J] [Group J'] (e : J ≃* J') (t : J) :
    MulAut.congr e (MulAut.conj t) = MulAut.conj (e t) := by
  ext x
  simp [MulAut.congr_apply]

theorem lu_conj_mk_eq_innerDiagonalAction {n : ℕ} {K : Type} [Field K]
    (g : SpecialLinearGroup (Fin n) K) :
    MulAut.conj ((QuotientGroup.mk' (center (SpecialLinearGroup (Fin n) K)) g :
        ProjectiveSpecialLinearGroup (Fin n) K)) =
      innerDiagonalAction n K (SpecialLinearGroup.toGL g) := by
  ext y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (center (SpecialLinearGroup (Fin n) K)) y
  rw [innerDiagonalAction_mk, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [slConjugation_matrix]
  simp [Matrix.inv_def, g.2]

theorem psl_inner_modelIn {J : Type} [Group J] {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSL n p f) (hm : Blueprint.LieModel J .PSL n p f) {t : J}
    (ht : orderOf (MulAut.conj t) = 2) {Kc : Subgroup (fixedSubgroup (MulAut.conj t))}
    (hKc : IsComponent Kc) : ModelIn p (luLinTuples n f) Kc := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_psl_of_lieModel hadm hm
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (center (SpecialLinearGroup (Fin n) K)) (e t)
  have hγ : MulAut.congr e (MulAut.conj t) =
      innerDiagonalAction n K (SpecialLinearGroup.toGL g) := by
    rw [← lu_conj_mk_eq_innerDiagonalAction, hg, lu_congr_conj]
  have hβ : orderOf (innerDiagonalAction n K (SpecialLinearGroup.toGL g)) = 2 := by
    rw [← hγ]
    exact (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective _).trans ht
  exact modelIn_of_component_equiv ((luFixedEquiv e _).trans
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ)))
    (fun L hL => inner_psl_modelIn hp hp2 hK hadm _ hβ hL) hKc

theorem psu_inner_modelIn {J : Type} [Group J] {n p f : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSU n p f) (hm : Blueprint.LieModel J .PSU n p f) {t : J}
    (ht : orderOf (MulAut.conj t) = 2) {Kc : Subgroup (fixedSubgroup (MulAut.conj t))}
    (hKc : IsComponent Kc) : ModelIn p (luUniTuples n f) Kc := by
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := nonempty_mulEquiv_primeFormP_of_lieModel' hadm hm
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective (ψ t)
  let A : primeFormUnitary h (idGram K n) := ⟨(s : GL (Fin n) K), s.2.1⟩
  have hc : primeFormConjHom h (idGram K n) A =
      MulAut.conj (s : primeFormP h (idGram K n)) :=
    primeFormConjHom_eq_conj h (idGram K n) s
  have hγ : MulAut.congr ψ (MulAut.conj t) = primeFormConjHom h (idGram K n) A := by
    rw [hc, lu_congr_conj, hs]
  have hβ : orderOf (primeFormConjHom h (idGram K n) A) = 2 := by
    rw [← hγ]
    exact (orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective _).trans ht
  exact modelIn_of_component_equiv ((luFixedEquiv ψ _).trans
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ)))
    (fun L hL => inner_psu_modelIn h hp2 hadm _ hβ hL) hKc

end CFSG.OddStandard.HigherRank.LinUnit
