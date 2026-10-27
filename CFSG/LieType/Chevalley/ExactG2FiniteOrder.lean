module

public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

theorem exact_G2_finite_order
    (K : Type) [Field K] [Finite K] {q : ℕ} (hq : Nat.card K = q) :
    Nat.card (adjointGroup .G2 K) =
        q ^ 6 * (q ^ 2 - 1) ^ 2 * (q ^ 2 + q + 1) * (q ^ 2 - q + 1) ∧
      Nat.card (adjointGroup .G2 K) = q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1) ∧
      (Nat.card (adjointGroup .G2 K) : ℤ) =
        (q : ℤ) ^ 6 * ((q : ℤ) ^ 2 - 1) ^ 2 * ((q : ℤ) ^ 2 + q + 1) * ((q : ℤ) ^ 2 - q + 1) := by
  have h := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2 (K := K)
  rw [hq, CFSG.Open.ordG2] at h
  have hq1 : 1 ≤ q := hq ▸ Nat.card_pos
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ hq1
  have hqq : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hZ : (Nat.card (adjointGroup .G2 K) : ℤ) =
      (q : ℤ) ^ 6 * ((q : ℤ) ^ 2 - 1) ^ 2 * ((q : ℤ) ^ 2 + q + 1) * ((q : ℤ) ^ 2 - q + 1) := by
    rw [h]
    push_cast [h2, h6]
    ring
  refine ⟨?_, h, hZ⟩
  zify [h2, hqq]
  rw [hZ]

end CFSG.LieType.Chevalley
