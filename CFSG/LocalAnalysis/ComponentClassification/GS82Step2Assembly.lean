module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82KStatements
public import CFSG.LocalAnalysis.ComponentClassification.GS82FuseQ3Defs

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

theorem gs82Step2FuseStatementK_of_cases (hQ3 : GS82Step2FuseQ3) (hH : ∀ (X : Type) [Group X]
    [Finite X] (c : Eight2.CtxA0 X), ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃*
    alternatingGroup (Fin 10)) → ¬ (c.s.p = 3 ∧ c.s.f = 1) → False) :
    GS82Step2FuseStatementK := by
  intro X _ _ c hA _
  by_cases hq3 : c.s.p = 3 ∧ c.s.f = 1
  · exact hQ3 X c hA hq3.1 hq3.2
  · exact (hH X c hA hq3).elim

end CFSG.ComponentClassification.GSThmB
