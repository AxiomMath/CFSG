module

public import CFSG.CGT.Stroth77.DeviationGeneric
public import CFSG.CGT.Stroth77.StrothFrameD

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

theorem StrothTypeIndex.two_le_k_of_familyTwo {τ : StrothTypeIndex} (hfam : τ.m + 2 = τ.n)
    (hm : 2 ≤ τ.m) (i : Fin 3) : 2 ≤ τ.k i := by
  rw [τ.k_eq]
  fin_cases i <;> simp <;> omega

end CFSG.CGT.Stroth77
