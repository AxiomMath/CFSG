module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLBasic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Module

@[expose] def McLaughlinTypes : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)),
    (∃ S : Set (LinearMap.GeneralLinearGroup (ZMod 2) V), S.Nonempty ∧
      (∀ t ∈ S, CFSG.ComponentClassification.OutcomeLocal.IsF2Transvection t) ∧
      G = Subgroup.closure S) →
    (∀ W : Submodule (ZMod 2) V,
      (∀ g ∈ G, ∀ w ∈ W, (g : V →ₗ[ZMod 2] V) w ∈ W) → W = ⊥ ∨ W = ⊤) →
    UniquenessMaximal.IsMcLaughlinGroup ↥G

end CFSG.HardMathSupport.Solomon.Coordinator
