module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.RootCharHom
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE7Three7
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.Chevalley.SteinbergBNF4Block
public import CFSG.RankThree.PartOne.KA5L.Chain
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KA5L CFSG.RankThree.Classical2 CFSG.Open
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.E6 CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
open scoped Matrix MatrixGroups Pointwise

section Orbit

@[expose] def e7T3A2Roots : Finset (Fin Tag.E7.rank → ℤ) :=
  {toVec Tag.E7.rank [0, 1, 0, 0, 0, 0, 0], toVec Tag.E7.rank [0, 0, 0, 1, 0, 0, 0],
    toVec Tag.E7.rank [0, 1, 0, 1, 0, 0, 0], toVec Tag.E7.rank [0, -1, 0, 0, 0, 0, 0],
    toVec Tag.E7.rank [0, 0, 0, -1, 0, 0, 0], toVec Tag.E7.rank [0, -1, 0, -1, 0, 0, 0]}

theorem e7T3A2Roots_eq :
    e7T3A2Roots = (rootFinset Tag.E7).filter
      (fun γ => ∀ i, i ∉ ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) →
        γ i = 0) := by
  decide +kernel

theorem mem_parabolicRoots_iff_mem_e7T3A2Roots {γ : Fin Tag.E7.rank → ℤ} :
    γ ∈ parabolicRoots Tag.E7 ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _) ↔
      γ ∈ e7T3A2Roots := by
  simp only [e7T3A2Roots_eq, Finset.mem_filter, mem_rootFinset, parabolicRoots,
    Set.mem_setOf_eq]

@[expose] noncomputable def e7T3A5Transport : WeylGroup Tag.E7 :=
  (coxeterSystem Tag.E7).wordProd e7T3CertA5.w

@[expose] def e7T3A5SubA2 : Set (Fin Tag.E7.rank → ℤ) :=
  (fun γ => e7T3A5Transport • γ) ''
    parabolicRoots Tag.E7 ({(1 : Fin Tag.E7.rank), (3 : Fin Tag.E7.rank)} : Set _)

end Orbit

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE7Three
