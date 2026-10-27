module

public import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6G23Cited
public import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6Kappa
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Kappa
import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6G23Discharge
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6Reduction
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
import CFSG.LocalAnalysis.AGLEmbedding.AscEightFourAux
import CFSG.LocalAnalysis.AGLEmbedding.AscTenThreeModule
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizerAux
import CFSG.LocalAnalysis.AGLEmbedding.CharCore
import CFSG.LocalAnalysis.AGLEmbedding.EscapeTwoCore
import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeConfig
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasic
import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockStructure
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3A6CubeN
import CFSG.LocalAnalysis.AGLEmbedding.ZOneFacts
import Mathlib.Data.Nat.ModEq
import Mathlib.Dynamics.FixedPoints.Defs
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.Fitting.CharacteristicP
import Mathlib
import CFSG.Quasithin.Background.Basic
import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellElem
import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
import CFSG.Quasithin.EmptyFaithful.S1414Group
import CFSG.Quasithin.Background.B6Basic
import CFSG.Quasithin.Background.C1GNNotation
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L28AutThree
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6CentralizingBase
import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.HardMathSupport.Cooperstein.Proving.BarTransport
import CFSG.HardMathSupport.Cooperstein.Coordinator.StarAux
import CFSG.LieType.BorelTits.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.RingTheory.SimpleModule.Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6Prop3
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIIASix
import CFSG.GH74.Uniqueness.SU.SU1Basic
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.AGLEmbedding.AThreePLiftAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosA
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosT
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111KappaMoves
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111NineThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111PsiLevel
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AFi22
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQShape
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedPhase3Main
import CFSG.HardMathSupport.Cooperstein.Transport
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6.G23
  CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def TwoRestNineSeventeen (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (z : H) (Kbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (L : Subgroup G)
    (hRM : R ≤ M), TwoRestG23Config P M H R Rbar z Kbar L →
    Hyp917R 3 M H (centBase M R L hRM) (innerNotQJ 3 H Kbar)

@[expose] def TwoRestRankTwoFactor (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (P : Sylow 3 G) (M H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
    (z : H) (Kbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (L : Subgroup G)
    (hRM : R ≤ M), TwoRestG23Config P M H R Rbar z Kbar L →
    AGLRankTwoFactorAt 3 M H (centBase M R L hRM) (innerNotQJ 3 H Kbar)

end CFSG.LocalAnalysis.RankThreeTheoremC
