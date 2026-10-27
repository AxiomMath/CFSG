module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTypes

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

@[expose] def SectionData : Prop :=
  ∃ (H' : Type) (_ : Group H') (_ : Finite H') (h' : Hyp59 H'),
    Nonempty (↥h'.T ⧸ h'.B.subgroupOf h'.T ≃* ↥h.T ⧸ h.B.subgroupOf h.T) ∧
    Nonempty (ZStarBar h'.K ≃* ZStarBar h.K) ∧ Nonempty (ZStarBar h'.J ≃* ZStarBar h.J) ∧
    (center (OddBar h.K) = ⊥ → Nonempty (OddBar h'.K ≃* OddBar h.K)) ∧
    (center (OddBar h.J) = ⊥ → Nonempty (OddBar h'.J ≃* OddBar h.J)) ∧
    (conjugate h'.K h'.a = h'.K ↔ conjugate h.K h.a = h.K) ∧
    (h'.a ∈ h'.K ⊔ coreActionKernel h'.K ↔ h.a ∈ h.K ⊔ coreActionKernel h.K) ∧
    (Nonempty (↥(generalizedFitting H') ≃* alternatingGroup (Fin 9)) →
      ∃ B₁ M : Subgroup H, IsPGroup 2 B₁ ∧ M ≤ centralizer (B₁ : Set H) ∧
        IsPComponent 2 (M.subgroupOf (centralizer (B₁ : Set H))) ∧
        Nonempty (ZStarBar M ≃* alternatingGroup (Fin 9))) ∧
    (Assembly.KProper Blueprint.Catalog H → Assembly.KProper Blueprint.Catalog H')

end Hyp52

end CFSG.ComponentClassification.GSThmB
