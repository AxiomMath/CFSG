module

public import CFSG.LocalAnalysis.OddStandard.Children
public import CFSG.ClassicalInvolution.Orders.OddLieType
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.McL.Simple
public import CFSG.Sporadic.Ly
public import CFSG.Sporadic.Suz.Simple
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.ON

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem card_eq_of_isSporadic {G : Type} [Group G] {s : TauCeti.SporadicName}
    (h : IsSporadic G s) : Nat.card G = Nat.card (Carrier s) :=
  Nat.card_congr h.some.toEquiv

theorem orderForm_of_oddOutcome
    {G : Type} [Group G] (h : OddOutcome G) :
    (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nat.card G ∈ lieOrdersChar p) ∨
      Nat.card G ∈ standardComponentOddSporadicOrders := by
  rcases h with h | h | h
  · exact .inl h
  · exact .inr (.inl (CFSG.ClassicalInvolution.card_mem_lieOrdersChar_of_oddLieType h))
  · refine .inr (.inr ?_)
    simp only [standardComponentOddSporadicOrders, standardComponentOrderM12,
      standardComponentOrderJ2, standardComponentOrderHe, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rcases h with h | h | h | h | h | h | h | h | h <;> rw [card_eq_of_isSporadic h]
    · rw [show Nat.card (Carrier .M12) = 95040 from CFSG.Sporadic.Mathieu.card_M12]; norm_num
    · rw [show Nat.card (Carrier .J1) = 175560 from CFSG.Sporadic.J1.card_J1]; norm_num
    · rw [show Nat.card (Carrier .J2) = 604800 from CFSG.Sporadic.J2.card_J2]; norm_num
    · rw [show Nat.card (Carrier .HS) = 44352000 from CFSG.Sporadic.HS.card_HS]; norm_num
    · rw [show Nat.card (Carrier .McL) = 898128000 from CFSG.Sporadic.McL.card_McL]; norm_num
    · rw [show Nat.card (Carrier .Ly) = 51765179004000000 from CFSG.Sporadic.Ly.card_Ly]
      norm_num
    · rw [show Nat.card (Carrier .Suz) = 448345497600 from CFSG.Sporadic.Suz.card_Suz]; norm_num
    · rw [show Nat.card (Carrier .He) = 4030387200 from CFSG.Sporadic.He.card_He]; norm_num
    · rw [show Nat.card (Carrier .ONan) = 460815505920 from CFSG.Sporadic.ON.card_ON]; norm_num

end CFSG.OddStandard
