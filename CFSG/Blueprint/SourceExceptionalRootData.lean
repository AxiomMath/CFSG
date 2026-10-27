module

public import CFSG.Blueprint.Chevalley

public noncomputable section

namespace CFSG.Blueprint.EvenSource

open CFSG.Blueprint.Chevalley Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem cartan_apply_self (τ : Tag) (i : Fin τ.rank) : τ.cartan i i = 2 := by
  cases τ <;> revert i <;> decide

end CFSG.Blueprint.EvenSource
