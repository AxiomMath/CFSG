module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLBalance
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma410
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankOneBranch
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitOddCoreReduction
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitOuterReduction
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSkeleton
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate110
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3085
public import Certificates.Certificate3120
public import Certificates.Certificate3170
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
public import Certificates.Certificate8046
public import Certificates.Certificate8048
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate9310
public import Certificates.Certificate9314
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Cover
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3CheckInputs
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Ly
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyCert
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Pattern
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLSide
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSquareProd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OneComp
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Choice
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSporadic
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISymplectic
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Props
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Open.GorensteinHaradaSectionalRankFourMilestoneDefs
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.RankThree.PartOne.LIT.RankMatrix
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.W2Lemma26A
public import Certificates.Certificate3085Base

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG

theorem footeInitialReductions_of_known_inputs
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) : FooteInitialReductions :=
  footeInitialReductions_of_lBalance footeLBalanceInput_holds hCI hGA hGC hSA

theorem footeRankBound_of_known_inputs_lb
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hSol : Sol76T13.SolomonThm13Simple)
    (hM3 : FooteSolomonFamilyInput) (h47 : FooteThm47Statement)
    (hAsc : Foote5.AschbacherCentralCoreInput) (h2An : GSThmB.Solomon2AnInput) : FooteRankBound :=
  footeRankBound_of_known_inputs_410 footeLBalanceInput_holds hCI hGA hSA hSol hM3 h47 hAsc h2An

theorem footeGeneralStatement_of_known_inputs
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hSol : Sol76T13.SolomonThm13Simple)
    (hM3 : FooteSolomonFamilyInput) (h47 : FooteThm47Statement)
    (hAsc : Foote5.AschbacherCentralCoreInput) (h2An : GSThmB.Solomon2AnInput)
    (h5 : FooteRankTwoExclusion) : FooteGeneralStatement :=
  footeGeneralStatement_of_steps (footeInitialReductions_of_known_inputs hCI hGA hGC hSA)
    (footeRankBound_of_known_inputs_lb hCI hGA hSA hSol hM3 h47 hAsc h2An) h5

theorem footeMaximalInput_of_known_inputs
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hGC : TBLit.GriessMultipliersCentralCovers)
    (hSA : SolAltLit.SchurAlternatingMultiplierInput) (hSol : Sol76T13.SolomonThm13Simple)
    (hM3 : FooteSolomonFamilyInput) (h47 : FooteThm47Statement)
    (hAsc : Foote5.AschbacherCentralCoreInput) (h2An : GSThmB.Solomon2AnInput)
    (h5 : FooteRankTwoExclusion)
    (hcore : ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
      Assembly.KProper Blueprint.Catalog X → FooteCoreHypothesis X) :
    FooteMaximalInput :=
  footeMaximalInput_of_general
    (footeGeneralStatement_of_known_inputs hCI hGA hGC hSA hSol hM3 h47 hAsc h2An h5) hcore

end CFSG.ComponentClassification.FooteLit
