module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveVeeSplitMain
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveOmeMain

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.Fischer

theorem veeFrobEquiv_ne_one : veeFrobEquiv ≠ 1 := veeFrobEquiv_ne_refl

theorem lFiveWOneFieldModuleInput_holds :
    LFiveWOneFieldModuleInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt _ c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hfield S₀ hS₀
  obtain ⟨D, β, hDs, hDk, hDt, hS₀U, hβb, hβa, hβc, hβt⟩ :=
    exists_wOne_normCoordinates hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hfield hS₀
  refine ⟨F4, inferInstance, inferInstance, inferInstance, veeFrobEquiv,
    by rw [Nat.card_eq_fintype_card, F4.card], veeFrobEquiv_ne_one, veeFrobHom_veeFrobHom, D, β,
    hDs, hDk, fun n m hm => ?_, hS₀U, hβb, hβa, hβc, hβt⟩
  rw [hDt n m hm, coe_veeFrob]
  rfl

end CFSG.SeitzReduction.LinearPilot
