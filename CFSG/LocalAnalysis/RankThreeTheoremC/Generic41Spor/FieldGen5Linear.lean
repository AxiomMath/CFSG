module

public import Certificates.Certificate43
public import CFSG.Open.StatedDefs
public import CFSG.Open.LocalVocabulary
public import CFSG.RankThree.PartOne.CTP.SeitzField
import CFSG.LieType.SeitzGeneration.OuterLinearTwo
import CFSG.LieType.SeitzGeneration.HyperCoverLinear
import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnFieldAut
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.FieldGen5Sylow
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.SeitzThree
public import CFSG.RankThree.PartOne.CTP.StrongPFinal
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.ClassicalInvolution.WeakCT.StandardPair
import CFSG.Foundations
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.CurtisTits.SpecialLinear
import CFSG.LieType.SeitzGeneration.HyperLinear
import CFSG.LieType.SeitzGeneration.OrthExLift
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
import CFSG.LocalAnalysis.ComponentClassification.GSLitType
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.RankThree.PartOne.CTP.SeitzLinear
import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
import CFSG.RankThree.PartOne.KC.LinearDegreeFive
import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Sporadic.Th.F2Spec
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThree.PartOne.CTP CFSG.LieType.SeitzGeneration

theorem exists_elemAbelian_diagThree_psl {K : Type} [Field K] [Finite K] {n p : ℕ}
    (hp : p.Prime) (hn : 5 ≤ n) (hpK : p ∣ Nat.card K - 1) :
    ∃ E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) K),
      IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  set Z : Subgroup Kˣ := Subgroup.zpowers ζ with hZ
  have hZcard : Nat.card Z = p := by rw [hZ, Nat.card_zpowers, hζ]
  have hZpow : ∀ a ∈ Z, a ^ p = 1 := fun a ha =>
    orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ orderOf_dvd_of_mem_zpowers ha)
  let ρ : Kˣ × Kˣ × Kˣ →* Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) K :=
    (QuotientGroup.mk' _).comp (diagThree m K)
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact diagThree_injective (by omega) ((eq_one_of_diagThree_mem_center (by omega)
      ((QuotientGroup.eq_one_iff _).1 hx)).trans (map_one _).symm)
  refine ⟨(Z.prod (Z.prod Z)).map ρ, ⟨inferInstance, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_prod, Subgroup.mem_prod] at hx
    have hxp : x ^ p = 1 :=
      Prod.ext (hZpow _ hx.1) (Prod.ext (hZpow _ hx.2.1) (hZpow _ hx.2.2))
    rw [← map_pow, hxp, map_one]
  · rw [Subgroup.card_map_of_injective hρ, Nat.card_congr (Subgroup.prodEquiv Z _).toEquiv,
      Nat.card_prod, Nat.card_congr (Subgroup.prodEquiv Z Z).toEquiv, Nat.card_prod, hZcard]
    ring

section Linear


theorem fieldAutData_five_psl {L : Type} [Group L] [Finite L] {n ℓ f : ℕ}
    (hM : StatedClassicalModel L .PSL n ℓ f) (hℓ : ℓ ≠ 5)
    (hcyc : ∀ S : Sylow 5 L, IsCyclic (S : Subgroup L)) : FieldAutData L 5 := by
  obtain ⟨⟨hℓp, hf, hn, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hM
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
  · refine FieldAutData.of_mulEquiv
      (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)
      Nat.prime_five ?_
    by_cases h2 : ringChar K = 2
    · exact fieldAutData_psl2_even_odd_prime Nat.prime_five (by norm_num) (by omega) h2
    · exact fieldAutData_psl2_odd_prime Nat.prime_five (by norm_num) h2
  · have : CharP K ℓ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓp hf hK
    refine FieldAutData.of_mulEquiv ((e.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
        (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
          n K)) Nat.prime_five ?_
    refine CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.fieldAutData_projectiveSL_of_cop
      hn3 Nat.prime_five (by norm_num) hℓp (Ne.symm hℓ) hf hK
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 fun hd => ?_)
    obtain ⟨E, hE, hEcard⟩ := exists_elemAbelian_diagThree_psl (K := K) Nat.prime_five
      (Nat.le_of_dvd (by omega) (hd.trans (Nat.gcd_dvd_left _ _)))
      (hd.trans (Nat.gcd_dvd_right _ _))
    let φ : Matrix.ProjectiveSpecialLinearGroup (Fin n) K ≃* L :=
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).trans e.symm
    exact false_of_isElemAbelian_of_cyclic_sylow hcyc (hE.map φ.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective, hEcard]; norm_num)

end Linear

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
