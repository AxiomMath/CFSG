module

public import CFSG.FeitThompson.Definitions.NormalSylowHallCore
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
import CFSG.FeitThompson.Local.HallCoreLargestNilpotentNormalHall
import CFSG.FeitThompson.Foundations.NormalNilpotentInFitting
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X] [Finite X]

theorem isGreatest_fittingRaw (X : Type*) [Group X] [Finite X] :
    IsGreatest {N : Subgroup X | N.Normal ∧ Group.IsNilpotent N} (fittingRaw X) :=
  ⟨⟨fittingRaw_normal X, fittingRaw_isNilpotent X⟩,
    fun _ h => le_fittingRaw_of_normal_of_isNilpotent h.1 h.2⟩

theorem eq_fittingRaw_of_isGreatest {N : Subgroup X}
    (h : IsGreatest {N : Subgroup X | N.Normal ∧ Group.IsNilpotent N} N) : N = fittingRaw X :=
  h.unique (isGreatest_fittingRaw X)

theorem hallCore_eq_fittingRaw_iff :
    hallCore X = fittingRaw X ↔ Nat.Coprime (Nat.card (fittingRaw X)) (fittingRaw X).index :=
  ⟨fun h => h ▸ coprime_natCard_index_hallCore, fun h =>
    le_antisymm hallCore_le_fittingRaw
      (le_hallCore_of_normal_of_isNilpotent_of_coprime (fittingRaw_normal X)
        (fittingRaw_isNilpotent X) h)⟩

end

end CFSG.FeitThompson
