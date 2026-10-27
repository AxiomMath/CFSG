module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PCSporBase
public import CFSG.GH74.KGroups.TwoM12Fixed

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.PCSpor

open CFSG Subgroup CFSG.Blueprint

theorem false_of_m12
    {Y : Type} [Group Y] [Finite Y] {β : MulAut Y} {T : Subgroup Y} (h : Setting Y β T)
    (hTtop : T ≠ ⊤) (hZ : Nat.card (center Y) = 2)
    (e : Y ⧸ center Y ≃* NativeSporadic.Carrier .M12) : False := by
  have hβ1 : β ≠ 1 := fun hβ => hTtop (h.eq_top_of_eq_one hβ)
  have hβ2 : β * β = 1 := MulEquiv.ext fun y => h.inv y
  have h60 := GH74.KGroups.TwoM12.card_le_sixty_of_fixed ⟨h.quasisimple, hZ, ⟨e⟩⟩ β hβ2 hβ1
    h.commutator_eq (fun x hx =>
      (LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff).1 (h.le hx))
  have h120 := h.card_ge
  omega

end CFSG.ComponentClassification.GS82PumpInputs.PCSpor
