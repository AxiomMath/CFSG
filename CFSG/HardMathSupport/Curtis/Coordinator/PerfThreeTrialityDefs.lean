module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.Open

@[expose] def TrialityFlagInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G], StatedClassicalModel G .POmegaPlus 4 2 1 →
    ∀ (J : Subgroup G) (T : Sylow 2 G), Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ J →
      J ≠ ⊤ → ∀ E : Subgroup G, E ≤ J → IsPGroup 3 E → ∀ x ∈ E, ∀ y ∈ E, x * y = y * x

end CFSG.HardMathSupport.Curtis.Coordinator
