module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Numerics
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporHN
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HN
public import CFSG.Sporadic.HNSchreier.Order
public import CFSG.Sporadic.HNSchreier.Intrinsic
public import CFSG.Sporadic.HNSchreier.ThreeCent
public import CFSG.Sporadic.HNSchreier.AltCent
public import CFSG.Sporadic.HNSchreier.Faithful
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.ClassicalGroups
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporAssemble
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Sporadic.HNSchreier

set_option maxRecDepth 20000 in
theorem nonempty_jh_equiv (hbr : SporadicBridges) :
    Nonempty (↥JH ≃* (TauCeti.CFSGIndex.sporadic .HN).Group) := by
  have e0 : NativeSporadic.HN ≃* (TauCeti.CFSGIndex.sporadic .HN).Group := (hbr .HN).some
  exact ⟨hnEquivJ.symm.trans e0⟩

set_option maxRecDepth 20000 in
theorem sporL3DownInner_HN
    (hbr : SporadicBridges) : SporL3DownInner .HN := by
  haveI : Finite ↥JH := Nat.finite_of_card_ne_zero (by rw [card_JH]; norm_num)
  have h1 := @sporL3DownInner_of_comp .HN ↥JH inferInstance inferInstance (nonempty_jh_equiv hbr)
  have h2 := h1 (by rw [card_JH]; exact noL3Eq_273030912000000)
  refine h2 ?_
  intro x hx
  rcases (order_three_classes x).1 hx with h | h
  · refine noL3Comp_centralizer_of_isConj h ?_
    have hL : IsSimpleGroup ↥L1J := by
      have := alt3_simple
      exact MulEquiv.isSimpleGroup (alt3.equivMapOfInjective iotaA iotaA_injective).symm
    have hcardL : Nat.card ↥(L1J) = 181440 := by
      rw [show (L1J : Subgroup JH) = alt3.map iotaA from rfl,
        Subgroup.card_map_of_injective iotaA_injective, card_alt3]
    refine noL3Comp_of_derived_simple (C := CJ (sJ 0)) gLAPPrimeCoreOf_CJ_s1 ?_ ?_
    · rw [commutator_CJ_s1]
      exact hL
    · rw [commutator_CJ_s1, hcardL]
      exact noL3Eq_181440
  · refine noL3Comp_centralizer_of_isConj h (noL3Comp_of_noDvd (C := CJ (sJ 2)) ?_)
    rw [card_CJ_s3]
    exact noL3Dvd_29160

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
