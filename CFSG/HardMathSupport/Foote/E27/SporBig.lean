module

public import CFSG.HardMathSupport.Foote.E27.SporList
public import CFSG.HardMathSupport.Foote.E27.SporCo2
public import CFSG.HardMathSupport.Foote.E27.SporCo3
public import CFSG.HardMathSupport.Foote.E27.SporFi22
public import CFSG.HardMathSupport.Foote.E27.SporFi23
public import CFSG.HardMathSupport.Foote.E27.SporFi24
public import CFSG.HardMathSupport.Foote.E27.SporHN
public import CFSG.HardMathSupport.Foote.E27.SporJ3
public import CFSG.HardMathSupport.Foote.E27.SporLy
public import CFSG.HardMathSupport.Foote.E27.SporMcL
public import CFSG.HardMathSupport.Foote.E27.SporSuz
public import CFSG.HardMathSupport.Foote.E27.SporB
public import CFSG.RankThree.PartOne.TCB.Sporadic
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockOddPairOrbitInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockProperSupportOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CommutingFamilyCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringDoubleCover
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporCo327
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Recognition.McLASThreeCount
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.M24
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate131101Base
public import Certificates.Certificate16005
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3176
public import Certificates.Certificate3179
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Blueprint

@[expose] def E27SporAt (s : TauCeti.SporadicName) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K R T : Subgroup X) (z : X), E27Config X K R T z → z ∈ K →
    Nonempty (↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group) → False

section Certificates


theorem e27SporBig_of_open (hCo1 : E27SporAt .Co1) (hTh : E27SporAt .Th) (hM : E27SporAt .M) :
    E27SporBig := by
  have hbr := CFSG.RankThree.PartOne.TCB.nonempty_carrier_mulEquiv_group
  refine e27SporBig_of_names hbr fun X _ _ K R T z hc hz s hs e => ?_
  simp only [sporBigNames, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hc.false_of_sporadic_j3 hz (hbr _) e.some
  · exact hc.false_of_sporadic_mcl hz (hbr _) e.some
  · exact hc.false_of_sporadic_suz hz (hbr _) e.some
  · exact hc.false_of_sporadic_ly hz (hbr _) e.some
  · exact hCo1 X K R T z hc hz e
  · exact hc.false_of_sporadic_co2 hz (hbr _) e.some
  · exact hc.false_of_sporadic_co3 hz (hbr _) e.some
  · exact hc.false_of_sporadic_fi22 hz (hbr _) e.some
  · exact hc.false_of_sporadic_fi23 hz (hbr _) e.some
  · exact hc.false_of_sporadic_fi24 hz (hbr _) e.some
  · exact e27_not_HN (hbr .HN) hc hz e
  · exact hTh X K R T z hc hz e
  · exact e27_not_B (hbr .B) hc hz e
  · exact hM X K R T z hc hz e

end Certificates

end CFSG.HardMathSupport.Foote.E27
