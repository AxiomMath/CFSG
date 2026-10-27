module

public import CFSG.Open.StatedDefs
import CFSG.Open.StatedAPI
import CFSG.GroupTheory.WeirSylow.CrossRankLinear
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDOrthBT
import CFSG.Blueprint.SourceQuadraticClassification
import CFSG.HardMathSupport.Malle.E27Lie.Defining.TypeD
import CFSG.Certificates.CentralKernel
import CFSG.Certificates.CosetTableWalkC
import CFSG.Certificates.FusionF2
import CFSG.Certificates.LiftedSchreierData
import CFSG.Certificates.WordSubgroupHom
import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
import CFSG.CharacterTheory.Semidihedral.ElementStructure
import CFSG.CharacterTheory.Semidihedral.Principal.DegreeZeroGram
import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
import CFSG.Fischer.UnitaryAction
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.LieType.Chevalley.EvenRootCommutatorF4
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.SpinOmega
import CFSG.LieType.Universal.Unitary
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDMain
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Weak
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicProof
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.Monster.AxisCount.HSIdentBaby
import CFSG.Monster.AxisCount.HSIdentRec0
import CFSG.Monster.AxisCount.HSIdentRec1
import CFSG.Monster.AxisCount.HSIdentRec2
import CFSG.Monster.AxisCount.HSIdentRec3
import CFSG.Monster.AxisCount.HSIdentRec4
import CFSG.Monster.AxisCount.HSIdentRec5
import CFSG.Monster.AxisCount.HSIdentRec6
import CFSG.Monster.AxisCount.HSIdentRec7
import CFSG.Monster.AxisCount.HSIdentSmall
import CFSG.RankThree.PartOne.CTP.StrongPClassification
import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicOpen
import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
import CFSG.RankThree.PartTwo.Sec4.Census.Interface
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Sporadic.Bridge.Catalogue
import CFSG.Sporadic.Bridge.M11CheckInputs
import CFSG.Sporadic.Presentation.Co2Base
import CFSG.Sporadic.Presentation.Co2Cover
import CFSG.Sporadic.Presentation.Co2Fusion
import CFSG.Sporadic.Presentation.Co2FusionInputs
import CFSG.Sporadic.Presentation.McLExactData
import CFSG.Sporadic.Presentation.McLExactInputs
import CFSG.Sporadic.Schreier.RuLOdd
import CFSG.Sporadic.Schreier.RuZClass
import CFSG.Sporadic.Schreier.TitsOther
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
import CFSG.Walter.Ree.Model.JTHyp
import CFSG.YGroups.DCE.B433Check
import Certificates.Certificate1
import Certificates.Certificate10
import Certificates.Certificate1000
import Certificates.Certificate1001
import Certificates.Certificate1001Base
import Certificates.Certificate1002
import Certificates.Certificate10027
import Certificates.Certificate1003
import Certificates.Certificate1004
import Certificates.Certificate1006
import Certificates.Certificate1007
import Certificates.Certificate1007Base
import Certificates.Certificate1008
import Certificates.Certificate1009
import Certificates.Certificate1009Base
import Certificates.Certificate1010
import Certificates.Certificate10107
import Certificates.Certificate10108
import Certificates.Certificate1011
import Certificates.Certificate10110
import Certificates.Certificate10111
import Certificates.Certificate1013
import Certificates.Certificate1014
import Certificates.Certificate1014Base
import Certificates.Certificate1015
import Certificates.Certificate1017
import Certificates.Certificate1018
import Certificates.Certificate1018Base
import Certificates.Certificate1019
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate16018
import Certificates.Certificate16041
import Certificates.Certificate2
import Certificates.Certificate2098
import Certificates.Certificate2103
import Certificates.Certificate2108
import Certificates.Certificate2109
import Certificates.Certificate2111
import Certificates.Certificate2112
import Certificates.Certificate2130
import Certificates.Certificate2135
import Certificates.Certificate2136
import Certificates.Certificate2139
import Certificates.Certificate2140
import Certificates.Certificate2145
import Certificates.Certificate2154
import Certificates.Certificate2160
import Certificates.Certificate2166
import Certificates.Certificate2173
import Certificates.Certificate2178
import Certificates.Certificate2179
import Certificates.Certificate2191
import Certificates.Certificate2192
import Certificates.Certificate2195
import Certificates.Certificate2198
import Certificates.Certificate2207
import Certificates.Certificate2211
import Certificates.Certificate2213
import Certificates.Certificate2215
import Certificates.Certificate2216
import Certificates.Certificate2216Base
import Certificates.Certificate2217
import Certificates.Certificate2224
import Certificates.Certificate2225
import Certificates.Certificate2225Base
import Certificates.Certificate2233
import Certificates.Certificate2233Base
import Certificates.Certificate2234
import Certificates.Certificate2235
import Certificates.Certificate2238
import Certificates.Certificate2239
import Certificates.Certificate2242
import Certificates.Certificate2243
import Certificates.Certificate2244
import Certificates.Certificate2245
import Certificates.Certificate2246
import Certificates.Certificate2251
import Certificates.Certificate2254
import Certificates.Certificate2254Base
import Certificates.Certificate2255
import Certificates.Certificate2274
import Certificates.Certificate2293
import Certificates.Certificate2294
import Certificates.Certificate2304
import Certificates.Certificate2305
import Certificates.Certificate2308
import Certificates.Certificate2323
import Certificates.Certificate3
import Certificates.Certificate3037
import Certificates.Certificate3037Base
import Certificates.Certificate3038
import Certificates.Certificate3038Base
import Certificates.Certificate3046
import Certificates.Certificate3148
import Certificates.Certificate3148Base
import Certificates.Certificate3150
import Certificates.Certificate3150Base
import Certificates.Certificate3151
import Certificates.Certificate3151Base
import Certificates.Certificate3152
import Certificates.Certificate3152Base
import Certificates.Certificate3153
import Certificates.Certificate3153Base
import Certificates.Certificate3154
import Certificates.Certificate3154Base
import Certificates.Certificate3157
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate6006
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate9
import Certificates.Certificate9124
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A9Lin

open CFSG.Open

private theorem eq_one_of_cube_eq_one_of_pow_eq_one {K : Type} [Field K] {c : Kˣ} {k l : ℕ}
    (h3 : c ^ 3 = 1) (hk : c ^ k = 1) (hl : c ^ l = 1)
    (h : Nat.Coprime 3 k ∨ ¬ 3 ∣ l) : c = 1 := by
  have hd1 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rcases h with hcop | hndvd
  · have hd : orderOf c ∣ Nat.gcd 3 k := Nat.dvd_gcd hd1 (orderOf_dvd_of_pow_eq_one hk)
    rw [show Nat.gcd 3 k = 1 from hcop] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  · have hd2 : orderOf c ∣ l := orderOf_dvd_of_pow_eq_one hl
    rcases (Nat.dvd_prime Nat.prime_three).mp hd1 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exact absurd (h1 ▸ hd2) hndvd

private theorem cube_eq_one_of_scalar_cube_eq_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {c : Kˣ} (i : ι)
    (h : (Matrix.GeneralLinearGroup.scalar ι c) ^ 3 = 1) : c ^ 3 = 1 := by
  apply Units.ext
  have h' : Matrix.GeneralLinearGroup.scalar ι (c ^ 3) = 1 := by rw [map_pow, h]
  have h'' := congrArg (fun g : GL ι K => ((g : Matrix ι ι K) i i)) h'
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_pow]
    using h''

theorem eq_one_of_mem_statedSL_of_mem_statedScalars {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : Nat.Coprime 3 n ∨ ¬ 3 ∣ Nat.card K - 1) {g : GL (Fin n) K}
    (hg : g ∈ StatedSL n K) (hs : g ∈ StatedScalars (Fin n) K) (h3 : g ^ 3 = 1) : g = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · exact Units.ext (Subsingleton.elim _ _)
  obtain ⟨c, rfl⟩ := hs
  have hc3 : c ^ 3 = 1 := cube_eq_one_of_scalar_cube_eq_one ⟨0, hnpos⟩ h3
  have hcn : c ^ n = 1 :=
    CFSG.GroupTheory.WeirSylow.pow_eq_one_of_scalar_mem_statedSL hg
  have hcK : c ^ (Nat.card K - 1) = 1 := by
    have := pow_card_eq_one' (x := c)
    rwa [Nat.card_units] at this
  rw [eq_one_of_cube_eq_one_of_pow_eq_one hc3 hcn hcK hn, map_one]

theorem eq_one_of_mem_statedSU_of_mem_statedScalars {K : Type} [Field K] [Finite K]
    {p f n : ℕ} (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2)
    (hn : Nat.Coprime 3 n ∨ ¬ 3 ∣ p ^ f + 1) {g : GL (Fin n) K}
    (hg : g ∈ StatedSU n (p ^ f) K) (hs : g ∈ StatedScalars (Fin n) K) (h3 : g ^ 3 = 1) :
    g = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · exact Units.ext (Subsingleton.elim _ _)
  obtain ⟨c, rfl⟩ := hs
  have hc3 : c ^ 3 = 1 := cube_eq_one_of_scalar_cube_eq_one ⟨0, hnpos⟩ h3
  obtain ⟨hcn, hcq⟩ := (CFSG.LinearGroups.scalar_mem_statedSU_iff hp hK hnpos c).1 hg
  rw [eq_one_of_cube_eq_one_of_pow_eq_one hc3 hcn hcq hn, map_one]

theorem eq_one_of_mem_statedSp_of_mem_statedScalars {K : Type} [Field K] {n : ℕ}
    {g : GL (Fin n ⊕ Fin n) K} (hg : g ∈ StatedSp n K)
    (hs : g ∈ StatedScalars (Fin n ⊕ Fin n) K) (h3 : g ^ 3 = 1) : g = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · exact Units.ext (Subsingleton.elim _ _)
  obtain ⟨c, rfl⟩ := hs
  have hc2 : c ^ 2 = 1 := (CFSG.Open.StatedAPI.scalar_mem_statedSp_iff hnpos c).1 hg
  have hc3 : c ^ 3 = 1 := cube_eq_one_of_scalar_cube_eq_one (Sum.inl ⟨0, hnpos⟩) h3
  have hc1 : c = 1 := by
    have h : c ^ 3 = c := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, hc2, one_mul]
    rwa [h] at hc3
  rw [hc1, map_one]

theorem eq_one_of_mem_statedOmega_of_mem_statedScalars {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Q : (ι → K) → K}
    (hQ : ∀ (c : K) (v : ι → K), Q (c • v) = c ^ 2 * Q v) {v₀ : ι → K} (hv₀ : Q v₀ ≠ 0)
    {g : GL ι K} (hg : g ∈ StatedOmega Q) (hs : g ∈ StatedScalars ι K) (h3 : g ^ 3 = 1) :
    g = 1 := by
  have hg2 : g ^ 2 = 1 :=
    CFSG.HardMathSupport.Malle.E27Lie.sq_eq_one_of_mem_statedScalars hQ hv₀ hg hs
  have h : g ^ 3 = g ^ 2 * g := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]
  rw [h, hg2, one_mul] at h3
  exact h3

theorem eq_one_of_mem_statedOmega_statedQuadOdd_of_mem_statedScalars {K : Type} [Field K]
    (n : ℕ) {g : GL (Fin n ⊕ Fin n ⊕ Unit) K}
    (hg : g ∈ StatedOmega (StatedQuadOdd n K))
    (hs : g ∈ StatedScalars (Fin n ⊕ Fin n ⊕ Unit) K) (h3 : g ^ 3 = 1) : g = 1 := by
  obtain ⟨v₀, hv₀⟩ := CFSG.LocalAnalysis.RankFourTheoremC.quadOdd_exists_one (s := n) (K := K)
  refine eq_one_of_mem_statedOmega_of_mem_statedScalars
    (fun d v => CFSG.LocalAnalysis.RankFourTheoremC.quadOdd_smul d v) (v₀ := v₀) ?_ hg hs h3
  rw [hv₀]
  exact one_ne_zero

theorem eq_one_of_mem_statedOmega_statedQuadMinus_of_mem_statedScalars {K : Type} [Field K]
    (n : ℕ) (b c : K) {g : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K}
    (hg : g ∈ StatedOmega (StatedQuadMinus n K b c))
    (hs : g ∈ StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) (h3 : g ^ 3 = 1) :
    g = 1 := by
  obtain ⟨v₀, hv₀⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.quadMinus_exists_one (K := K) n b c
  refine eq_one_of_mem_statedOmega_of_mem_statedScalars
    (fun d v => CFSG.LocalAnalysis.RankFourTheoremC.quadMinus_smul n b c d v) (v₀ := v₀) ?_
    hg hs h3
  rw [hv₀]
  exact one_ne_zero

theorem finrank_le_three_of_statedQuadMinus_four {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {W : Submodule K (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → K)}
    (hW : ∀ w ∈ W, StatedQuadMinus 4 K b c w = 0) : Module.finrank K W ≤ 3 := by
  have h := CFSG.Blueprint.EvenSource.le_sourceWittIndex (StatedQuadMinus 4 K b c) hW
  rw [CFSG.Blueprint.EvenSource.sourceWittIndex_statedQuadMinus 4 K (by norm_num) hirr] at h
  simpa using h

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A9Lin
