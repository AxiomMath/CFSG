module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.Blueprint.Recognition.Exact

open NativeSporadic

@[expose] def OddStandardType (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
    OddLieType X ∨ LieModel X .PSL 3 2 2 ∨ IsSporadic X .He

end CFSG.Blueprint.Recognition.Exact
