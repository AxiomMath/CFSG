module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Frontier

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def GS82CaseA10EpsZeroInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : Eight2.Setting3 X),
    normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X) →
    Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10)) →
    ¬ ⁅s.Dt, s.h.S⁆ ≤ s.h.P → False

end CFSG.ComponentClassification.GSThmB
