module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBComm
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBReduce
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Q3.ModelCenter
public import CFSG.ClassicalInvolution.RouteD.LocalLift
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma26
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma39Bar
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Statement
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLSide
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFixedFactorSylowReduction
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsPSL2More
public import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Walter.J1Recog
public import CFSG.Walter.Ree.Thompson2.BaseFin
public import CFSG.Walter.ReeOrder.WardLocal
public import CFSG.Walter.W67.Section8.Prop83
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

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.RankTwoSporadic.B

open Subgroup CFSG.SectionRank CFSG.SectionRank.Native CFSG.Sporadic.SmallF2
open CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native
open CFSG.ComponentClassification.RankTwoSporadic.B.Native CFSG.Blueprint

@[expose] def PairFacts (C : MCert) (pr : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Prop :=
  MFact.ord pr.1 pr.2.2.2.1 ∈ C.facts ∧ MFact.ord pr.2.1 pr.2.2.2.2.1 ∈ C.facts ∧
    MFact.ord pr.2.2.1 pr.2.2.2.2.2 ∈ C.facts ∧
    MFact.eq [(pr.2.2.1, 1)] [(pr.1, 1), (pr.2.1, 1)] ∈ C.facts ∧
    pr.2.2.2.1.Coprime pr.2.2.2.2.1 ∧ pr.2.2.2.1.Coprime pr.2.2.2.2.2 ∧
    pr.2.2.2.2.1.Coprime pr.2.2.2.2.2

instance (C : MCert) (pr : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Decidable (PairFacts C pr) := by
  unfold PairFacts; infer_instance

end CFSG.ComponentClassification.RankTwoSporadic.B
