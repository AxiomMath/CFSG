module

public import CFSG.RankThree.PartOne.SEITZ3.MaxDefs
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.SEITZ3

namespace CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

theorem ordG2_closed (q : ℕ) (hq : 1 ≤ q) :
    CFSG.Open.ordG2 q =
      q ^ 2 * (q ^ 2 - 1) ^ 2 * (q ^ 4 * (q ^ 4 + q ^ 2 + 1)) := by
  rw [← CFSG.Timmesfeld.ExceptionalOrders.ordG2_eq q hq]
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have h1 : (r + 1) ^ 2 - 1 = r * (r + 2) := by
    apply Nat.sub_eq_of_eq_add; ring
  simp only [CFSG.Timmesfeld.ExceptionalOrders.geomSum, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, Nat.add_sub_cancel, h1]
  ring

end CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport
