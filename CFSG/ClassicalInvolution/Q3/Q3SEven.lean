module

public import CFSG.ClassicalInvolution.Q3.Q3SSylow
public import CFSG.ClassicalInvolution.Q3.Q3RSectionalFour
public import CFSG.ClassicalInvolution.SmallCases.EvenLie
public import CFSG.ClassicalInvolution.SmallCases.NobqL34
public import CFSG.LieType.Multipliers.Sz8Matrix
public import Certificates.Certificate113
public import Certificates.Certificate2022
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalInvolution.Balance.PassTwoConj
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.Q3.ClassicalFundamentalModels
public import CFSG.ClassicalInvolution.RankTwo
public import CFSG.ClassicalInvolution.RouteD.TypeAChain
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3CheckInputs
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
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
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISymplectic
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Sporadic.McL
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open scoped MatrixGroups

theorem noWeakClassical3_of_forall_orderOf_ne_four {F : Type} [Group F] [Finite F]
    (h : ∀ x : F, orderOf x ≠ 4) : NoWeakClassical3 F := fun L _ hL => by
  obtain ⟨y, -, hy⟩ := hL.exists_orderOf_eq_four
  exact h y hy

theorem noWeakClassical3_of_not_three_dvd_card {F : Type} [Group F] [Finite F]
    (h : ¬ 3 ∣ Nat.card F) : NoWeakClassical3 F := fun L _ hL =>
  h (hL.three_dvd_card.trans (Subgroup.card_subgroup_dvd_card L))

theorem orderOf_ne_four_psl_two {f : ℕ} (hf : 2 ≤ f) (x : PSL(2, GaloisField 2 f)) :
    orderOf x ≠ 4 := by
  intro hx
  have : Finite PSL(2, GaloisField 2 f) := Finite.of_surjective
    (QuotientGroup.mk : SL(2, GaloisField 2 f) → PSL(2, GaloisField 2 f))
    QuotientGroup.mk_surjective
  have hz : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨-, -, hexp, hZ, hQcard⟩ := bender_psl2_borel_full f hf Q
  have hcen : Subgroup.center (Q : Subgroup PSL(2, GaloisField 2 f)) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hZ, hQcard, pow_one]
  have hxQ : x ∈ (Q : Subgroup PSL(2, GaloisField 2 f)) := hQ (Subgroup.mem_zpowers x)
  have hmem : (⟨x, hxQ⟩ : (Q : Subgroup PSL(2, GaloisField 2 f))) ∈
      Subgroup.center (Q : Subgroup PSL(2, GaloisField 2 f)) := by
    rw [hcen]; exact Subgroup.mem_top _
  have h2 := hexp _ hmem
  have h3 : x ^ 2 = 1 := congrArg Subtype.val h2
  have := orderOf_dvd_of_pow_eq_one h3
  rw [hx] at this
  omega

theorem statedClassicalModel_of_lieModel_psl {G : Type} [Group G] {n p f : ℕ}
    (h : LieModel G .PSL n p f) (hn : n ≠ 0) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn h

theorem noWeakClassical3_of_psl_two {G : Type} [Group G] {f : ℕ} (hf : 2 ≤ f)
    (h : LieModel G .PSL 2 2 f) : NoWeakClassical3 G := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := statedClassicalModel_of_lieModel_psl h (by norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e' := e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 2 2 f (by omega) hK)
  have : Finite PSL(2, GaloisField 2 f) := Finite.of_surjective
    (QuotientGroup.mk : SL(2, GaloisField 2 f) → PSL(2, GaloisField 2 f))
    QuotientGroup.mk_surjective
  have : Finite G := Finite.of_equiv _ e'.symm.toEquiv
  refine noWeakClassical3_of_forall_orderOf_ne_four fun x hx => ?_
  exact orderOf_ne_four_psl_two hf (e' x) (by rw [MulEquiv.orderOf_eq]; exact hx)

theorem noWeakClassical3_of_suzuki_eight {G : Type} [Group G]
    (h : LieModel G .twistedB2 0 2 3) : NoWeakClassical3 G := by
  obtain ⟨e⟩ := CFSG.LieType.Multipliers.Sz8.nonempty_mulEquiv_suzukiGroup_of_blueprint h
  have hcard : Nat.card G = 29120 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.LieType.Multipliers.Sz8.card_suzukiGroup
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  refine noWeakClassical3_of_not_three_dvd_card ?_
  rw [hcard]
  norm_num

section PSL34

open CFSG.ComponentClassification.PSL3Four

theorem noWeakClassical3_S : NoWeakClassical3 ↥S := by
  intro L z hL
  have : Finite ↥S := inferInstance
  obtain ⟨y, hyL, hy⟩ := hL.exists_orderOf_eq_three
  have hz2 : (z : Equiv.Perm (Fin 42)) * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [hL.orderOf_eq_two, pow_two] at this
    simpa using congrArg Subtype.val this
  have hz1 : (z : Equiv.Perm (Fin 42)) ≠ 1 := by
    intro h1
    have : z = 1 := Subtype.ext h1
    exact hL.ne_one this
  obtain ⟨c, hcR, hc⟩ := CFSG.ClassicalInvolution.Nobq.exists_conj_r₁ z.2 hz1 hz2
  have hyz : (y : ↥S) * z = z * y := hL.mul_eq hyL
  have hcomm : ((y : ↥S) : Equiv.Perm (Fin 42)) * (z : Equiv.Perm (Fin 42)) =
      (z : Equiv.Perm (Fin 42)) * ((y : ↥S) : Equiv.Perm (Fin 42)) :=
    congrArg Subtype.val hyz
  have h64 := CFSG.ClassicalInvolution.Nobq.orderOf_dvd_sixtyfour hcR hc (y : ↥S).2 hcomm
  rw [Subgroup.orderOf_coe, hy] at h64
  omega

theorem noWeakClassical3_of_psl_three_four {G : Type} [Group G]
    (h : LieModel G .PSL 3 2 2) : NoWeakClassical3 G := by
  obtain ⟨e⟩ := nonempty_equiv_of_stated G (statedClassicalModel_of_lieModel_psl h (by norm_num))
  exact NoWeakClassical3.of_mulEquiv e noWeakClassical3_S

end PSL34

theorem noWeakClassical3_of_charTwo {G : Type} [Group G]
    (h : LieModel G .PSL 2 2 3 ∨ LieModel G .PSL 2 2 4 ∨ LieModel G .PSL 3 2 2 ∨
      LieModel G .twistedB2 0 2 3) : NoWeakClassical3 G := by
  rcases h with h | h | h | h
  · exact noWeakClassical3_of_psl_two (by norm_num) h
  · exact noWeakClassical3_of_psl_two (by norm_num) h
  · exact noWeakClassical3_of_psl_three_four h
  · exact noWeakClassical3_of_suzuki_eight h

end CFSG.ClassicalInvolution.Q3
