module

public import CFSG.Blueprint.ChevalleyPinned

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley


@[expose] def cosetRoots (τ : Tag) (k : Fin τ.rank) (n : ℕ) : Set (Fin τ.rank → ℤ) :=
  {α | IsRoot τ α ∧ (n : ℤ) ∣ α k}

@[expose] def FrameClosing (τ : Tag) (K : Type) [Field K] (S : Set (Fin τ.rank → ℤ)) : Prop :=
  ∀ H : Subgroup (ModGL τ K), H ≤ adjointGroup τ K → rootSpan τ K S ≤ H →
    ¬ H ≤ Subgroup.normalizer (rootSpan τ K S : Set (ModGL τ K)) → H = adjointGroup τ K

@[expose] def FrameNormalizerSolvable (τ : Tag) (K : Type) [Field K]
    (S : Set (Fin τ.rank → ℤ)) : Prop :=
  ∀ P : Subgroup (ModGL τ K), P ≤ adjointGroup τ K →
    P ≤ Subgroup.normalizer (rootSpan τ K S : Set (ModGL τ K)) →
    Group.IsSolvable ↥(P ⊓ rootSpan τ K S) → Group.IsSolvable ↥P

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
