module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CA7

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

@[expose] def GS82CaseA10Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : Eight2.Setting3 X),
    normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X) →
    Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10)) → False

@[expose] def GS82CaseAL4U4Input : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (c : Eight2.CtxA0 X),
    ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)) → False

end CFSG.ComponentClassification.GSThmB
