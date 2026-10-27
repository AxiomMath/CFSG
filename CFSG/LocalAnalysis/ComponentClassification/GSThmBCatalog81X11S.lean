module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Frontier

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

@[expose] def GS81Step11Input : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (h : Hyp59 H) (H₁ : h.L81Hyp) (d : H₁.Data) (v : H),
    d.Stage7 v → Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 3 2 →
      Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 3 1 →
      ∃ w ∈ h.U81 v, w ∉ h.S ∧ h.S ≤ h.P ⊔ (h.S ⊓ centralizer ({w} : Set H))

end CFSG.ComponentClassification.GSThmB
