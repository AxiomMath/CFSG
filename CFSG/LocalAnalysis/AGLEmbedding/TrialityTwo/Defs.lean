module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelBasic
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitFlagTransitivity

public noncomputable section

namespace CFSG.AGLEmbedding.TrialityTwo

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.LieType.Universal.Spin

@[expose] def IsSingularPoint {K : Type} [Field K] (W : Submodule K (Fin 4 ⊕ Fin 4 → K)) : Prop :=
  Module.finrank K W = 1 ∧ ∀ v ∈ W, StatedQuadPlus 4 K v = 0

@[expose] def fixedObjects {K : Type} [Field K] (g : StatedOmega (StatedQuadPlus 4 K)) :
    Set (Submodule K (Fin 4 ⊕ Fin 4 → K)) :=
  {W | (IsSingularPoint W ∨ W ∈ singularSubspaces (quadPlus 4 K) 4) ∧
    statedDerivedSubspaceAction (StatedQuadPlus 4 K) g W = W}

@[expose] def fixedObjectsStabilizer {K : Type} [Field K] (g : StatedOmega (StatedQuadPlus 4 K)) :
    Subgroup (StatedOmega (StatedQuadPlus 4 K)) :=
  ⨅ W ∈ fixedObjects g, statedDerivedSubspaceStabilizer (StatedQuadPlus 4 K) W

theorem self_mem_fixedObjectsStabilizer {K : Type} [Field K]
    (g : StatedOmega (StatedQuadPlus 4 K)) : g ∈ fixedObjectsStabilizer g := by
  simp only [fixedObjectsStabilizer, Subgroup.mem_iInf]
  intro W hW
  exact hW.2

@[expose] def FiveFixedDichotomy : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ g : StatedOmega (StatedQuadPlus 4 K), orderOf g = 5 →
      ((∃ W, IsSingularPoint W ∧ statedDerivedSubspaceAction (StatedQuadPlus 4 K) g W = W) ↔
        ¬ ∃ W ∈ singularSubspaces (quadPlus 4 K) 4,
          statedDerivedSubspaceAction (StatedQuadPlus 4 K) g W = W)

@[expose] def SevenFixedRigid : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ g : StatedOmega (StatedQuadPlus 4 K), orderOf g = 7 →
      fixedObjectsStabilizer g ≠ ⊥ ∧
      ⁅fixedObjectsStabilizer g, fixedObjectsStabilizer g⁆ = fixedObjectsStabilizer g ∧
      ∀ β : MulAut (fixedObjectsStabilizer g),
        β ⟨g, self_mem_fixedObjectsStabilizer g⟩ = ⟨g, self_mem_fixedObjectsStabilizer g⟩ →
          β ^ 3 = 1 → β = 1

end CFSG.AGLEmbedding.TrialityTwo
