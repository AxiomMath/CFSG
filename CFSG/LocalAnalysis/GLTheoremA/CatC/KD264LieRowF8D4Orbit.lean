module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.Classical.SteinbergBYOrthogonalGates
public import CFSG.RankThree.PartOne.CTP.StdMatrix
public import CFSG.RankThree.PartOne.FIVES.Lift
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

open Matrix Subgroup CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open scoped Pointwise

theorem exists_index_three_family {K : Type} [Field K] [Finite K] {d f : ℕ}
    (Q : QuadraticForm K (Fin d → K)) (hg : OrthogonalGates Q f)
    (A : Subgroup (MulAut (matrixProjectiveDerived Q))) :
    ∃ A₀ : Subgroup (MulAut (matrixProjectiveDerived Q)), A₀ ≤ A ∧ Nat.card A ≤ 3 * Nat.card A₀ ∧
      A₀ ≤ matrixProjectiveImage Q := by
  classical
  haveI : Finite (matrixProjectiveDerived Q) := inferInstance
  haveI : Finite (MulAut (matrixProjectiveDerived Q)) := Finite.of_injective
    (fun α : MulAut (matrixProjectiveDerived Q) => (α : matrixProjectiveDerived Q → matrixProjectiveDerived Q))
    (fun a b h => MulEquiv.ext (congrFun h))
  let x₀ : Set (Subgroup (matrixProjectiveDerived Q)) := projectivePointFamily Q
  have hX : (MulAction.orbit (MulAut (matrixProjectiveDerived Q)) x₀).ncard ≤ 3 := hg.2.2.2.1
  have hsub : MulAction.orbit A x₀ ⊆ MulAction.orbit (MulAut (matrixProjectiveDerived Q)) x₀ := by
    rintro _ ⟨a, rfl⟩
    exact ⟨(a : MulAut (matrixProjectiveDerived Q)), rfl⟩
  have horb : (MulAction.stabilizer A x₀).index ≤ 3 := by
    rw [MulAction.index_stabilizer]
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans hX
  refine ⟨(MulAction.stabilizer A x₀).map A.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective A.subtype_injective, ← Subgroup.card_mul_index
      (MulAction.stabilizer A x₀), mul_comm]
    exact Nat.mul_le_mul_right _ horb
  · rintro _ ⟨s, hs, rfl⟩
    have hs' : (s : MulAut (matrixProjectiveDerived Q)) • x₀ = x₀ := hs
    have hfam : (s : MulAut (matrixProjectiveDerived Q)) ∈ projectivePointFamilyAut Q := hs'
    rw [← hg.2.2.2.2.2.1]
    exact hfam

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Om

end
