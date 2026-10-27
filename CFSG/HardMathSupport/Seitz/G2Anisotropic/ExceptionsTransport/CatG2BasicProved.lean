module

public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.CatG2Basic
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

theorem g2ThreeCatBasic : G2ThreeCatBasic := by
  refine g2ThreeCatBasic_of_native ?_ ?_ ?_
  · intro q hv K _ _ hK
    exact CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv K hK
  · intro K _ _
    have h2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt (Finite.one_lt_card)
    have hq : 1 ≤ Nat.card K := by omega
    have hord := CFSG.Timmesfeld.ExceptionalOrders.ordG2_eq (Nat.card K) hq
    refine Nat.finite_of_card_ne_zero ?_
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, ← hord]
    have h3 : 0 < Nat.card K - 1 := by omega
    have h4 : 0 < Nat.card K ^ 6 := by positivity
    have h5 : ∀ s : ℕ, 0 < CFSG.Timmesfeld.ExceptionalOrders.geomSum s.succ 1 (Nat.card K) :=
      fun s => Finset.sum_pos' (fun _ _ => Nat.zero_le _)
        ⟨0, Finset.mem_range.2 (Nat.succ_pos s), by simp⟩
    have h6 := h5 1
    have h7 := h5 5
    positivity
  · intro K _ _
    exact CFSG.LieType.Chevalley.center_adjointGroup_eq_bot

end CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
