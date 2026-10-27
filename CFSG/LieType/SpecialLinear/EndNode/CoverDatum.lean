module

public import CFSG.LieType.SpecialLinear.CurtisDatum

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open scoped MatrixGroups

noncomputable section

variable (m : ℕ) (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

theorem coverId_datum_U :
    (coverId m F p).datum.U = (curtisDatum m F p).U := by
  change (coverId m F p).lU = (curtisDatum m F p).U
  refine le_antisymm ?_ ?_
  · intro x hx
    exact hx.1
  · intro x hx
    rw [CentralCoverData.mem_lU]
    refine ⟨hx, ?_⟩
    obtain ⟨k, hk⟩ := IsPGroup.exists_pow_pow_eq_one (curtisDatum m F p).isPGroup_U ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end

end CFSG.LieType.SpecialLinear
