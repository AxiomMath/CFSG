module

public import CFSG.GH74.Generic.BProg.B3.L2CompBasic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.BProg.B3.L2CompOrders

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.Blueprint Subgroup

theorem three_dvd_of_card {N q : ℕ} (h : N * 2 = q * (q ^ 2 - 1)) : 3 ∣ N := by
  have hq1 : 1 ≤ q ∨ q = 0 := by omega
  rcases hq1 with hq1 | rfl
  · have hQ : q * (q ^ 2 - 1) + q = q ^ 3 := by
      have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
      zify [h2]
      ring
    have hmod : q ^ 3 % 3 = (q % 3) ^ 3 % 3 := Nat.pow_mod q 3 3
    have h3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases h3 with h' | h' | h' <;> rw [h'] at hmod <;> norm_num at hmod <;> omega
  · simp at h
    omega

theorem sixty_le_card {N q : ℕ} (hq : 5 ≤ q) (h : N * 2 = q * (q ^ 2 - 1)) : 60 ≤ N := by
  have h1 : 24 ≤ q ^ 2 - 1 := by
    have : 25 ≤ q ^ 2 := by nlinarith
    omega
  have : 5 * 24 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq h1
  omega

theorem card_fixedIn_congr {X M : Type} [Group X] [Group M] (e : X ≃* M) (y : MulAut X) :
    Nat.card {x : M // MulAut.congr e y x = x} = Nat.card ↥(B2.fixedIn X (zpowers y)) := by
  refine (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => ?_)).symm
  have h : (MulAut.congr e y) (e x) = e (y x) := by
    rw [MulAut.congr_apply]
    simp
  rw [L2CompBasic.mem_fixedIn_zpowers_iff]
  show y x = x ↔ (MulAut.congr e y) (e x) = e x
  rw [h]
  exact ⟨fun h => by rw [h], fun h => e.injective h⟩

end CFSG.GH74.Generic.BProg.B3.L2CompOrders
