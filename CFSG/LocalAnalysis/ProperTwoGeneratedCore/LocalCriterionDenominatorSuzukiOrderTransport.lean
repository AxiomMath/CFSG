module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiOrders

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.MatrixGroups

variable {G : Type*} [Group G]

theorem suzuki_actual_full_centralizer_card
    {K : Type} [Field K] [Finite K] (a : ℕ) (ha : 1 ≤ a)
    (hcard : Nat.card K = 2 ^ (2 * a + 1)) (e : G ≃* GLASzGroup a K)
    (W : Subgroup G) (hWne : W ≠ ⊥)
    (hdiv : Nat.card W ∣ (Nat.card K) ^ 2 + 1)
    (hcentralizer : ∀ x ∈ W, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = W) :
    Nat.card W = Nat.card K - 2 ^ (a + 1) + 1 ∨
      Nat.card W = Nat.card K + 2 ^ (a + 1) + 1 := by
  let E : G ≃* SuzukiMatrixGroup a :=
    (e.trans (glaSzEquivNative a ha hcard)).trans (suzukiCoverNativeEquiv a)
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
  have hwG : (w : G) ≠ 1 := fun h => hw (Subtype.ext h)
  have horder : orderOf (w : G) ∣ (Nat.card K) ^ 2 + 1 :=
    (Subgroup.orderOf_coe w) ▸ (orderOf_dvd_natCard w).trans hdiv
  have hEw : E (w : G) ≠ 1 := by
    intro h
    exact hwG (E.injective (h.trans E.map_one.symm))
  have hEordereq : orderOf (E (w : G)) = orderOf (w : G) :=
    orderOf_injective E.toMonoidHom E.injective (w : G)
  have hEorder : orderOf (E (w : G)) ∣ (2 ^ (2 * a + 1)) ^ 2 + 1 := by
    rw [hEordereq, ← hcard]
    exact horder
  have hCcard : Nat.card (Subgroup.centralizer ({E (w : G)} : Set (SuzukiMatrixGroup a))) =
      Nat.card W := by
    rw [← Nat.card_congr (elementCentralizerEquiv E (w : G)).toEquiv,
      hcentralizer (w : G) w.property hwG]
  have h := suzuki_degree_divisor_entire_centralizer_exact_order a (by omega)
    (E (w : G)) hEw hEorder
  rw [hCcard, ← hcard] at h
  exact h

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
