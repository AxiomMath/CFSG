module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10SideA6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CA7
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputs

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.A10Side

@[expose] def GS82CentXA10TransferStatementK : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : Eight2.Setting3 X),
    normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X) →
    Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10)) →
    ¬ ⁅s.Dt, s.h.S⁆ ≤ s.h.P →
    ∀ (e : ↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J ≃* alternatingGroup (Fin 6)) (k : X)
      (hext : GrSLit.IsExtremalIn s.h.S (k⁻¹ * s.h.x * k)),
      IsSymSixType e (Eight.oddBarAction s.h.J ⟨k⁻¹ * s.h.x * k, s.h.S_le_normalizer hext.1⟩) →
      (∀ u ∈ s.h.S ⊓ centralizer ({s.h.x} : Set X),
        k⁻¹ * u * k ∈ s.h.S ⊓ centralizer ({k⁻¹ * s.h.x * k} : Set X)) →
      k * s.h.a * k⁻¹ ∈ coreActionKernel s.h.J

@[expose] def GS82Step2FuseStatementK : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (c : Eight2.CtxA0 X),
    ¬ Nonempty (↥(generalizedFitting (c.s.h.subQuot c.s.y)) ≃* alternatingGroup (Fin 10)) →
    (c.s.h.secG0 c.s.y).relIndex c.s.h.S ≠ 2 →
    ∃ g : X, g⁻¹ * c.s.h.a * g = c.s.h.a * c.b * c.Z.z ∧ g⁻¹ * c.Z.z * g = c.b

end CFSG.ComponentClassification.GSThmB
