module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Targets

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

open CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8

@[expose] def AEBlocks8' : Prop :=
  ∀ (α : Finset (Fin 8)) (hα : α.card = 4) (B : Set (Subgroup (AEQ 8))), IsBlock B →
    memBar α hα true ∈ B → memBar α hα false ∈ B →
    B = {memBar α hα true, memBar α hα false} ∨
      (∀ M ∈ B, ∃ (β : Finset (Fin 8)) (hβ : β.card = 4) (c : Bool), (β = α ∨ β = αᶜ) ∧
        M = memBar β hβ c) ∨ (∀ M, IsMember M → M ∈ B)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
