module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CA7

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def GS82Step2FuseQ3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (c : Eight2.CtxA0 X),
    ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)) →
    c.s.p = 3 → c.s.f = 1 →
    ∃ g : X, g⁻¹ * c.s.h.a * g = c.s.h.a * c.b * c.Z.z ∧ g⁻¹ * c.Z.z * g = c.b

end CFSG.ComponentClassification.GSThmB
