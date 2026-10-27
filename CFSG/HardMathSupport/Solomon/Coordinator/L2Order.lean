module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Cover

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def L2OrderUnique : Prop :=
  ∀ (Y : Type) [Group Y] (s s' : ℕ), LocalBalance.Lemma514CoverNs.IsTypeL2 s Y →
    LocalBalance.Lemma514CoverNs.IsTypeL2 s' Y → s = s' ∨ (s = 4 ∧ s' = 5) ∨ (s = 5 ∧ s' = 4)

end CFSG.HardMathSupport.Solomon.Coordinator
