module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.FritzII

variable (G : Type) [Group G]

@[expose] def FzAssumptionII : Prop :=
  ¬ ∀ P : Subgroup G, IsPGroup 2 P → ∃ s : Finset G, s.card ≤ 4 ∧ Subgroup.closure (s : Set G) = P

end CFSG.OddStandard.SmallF3.FritzII
