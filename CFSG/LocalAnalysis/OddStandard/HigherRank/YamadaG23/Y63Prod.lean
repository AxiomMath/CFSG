module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

theorem y63_card_mul_of_sup {G : Type} [Group G] [Finite G] {T M : Subgroup G} [M.Normal]
    (h : T ⊔ M = ⊤) : Nat.card ↥T * Nat.card ↥M = Nat.card G * Nat.card ↥(T ⊓ M) := by
  have h1 : M.relIndex T = M.index := by
    have := Subgroup.relIndex_sup_right (H := T) (K := M)
    rw [h, Subgroup.relIndex_top_right] at this
    exact this.symm
  have h2 := Subgroup.relIndex_mul_card (H := M) (K := T)
  rw [h1, inf_comm] at h2
  have h3 := Subgroup.index_mul_card (H := M)
  rw [← h2, ← h3]
  exact Nat.mul_right_comm _ _ _

theorem y63_squeeze {G : Type} [Group G] [Finite G] {B C T M : Subgroup G} [M.Normal]
    (hG : Nat.card G = 512) (hM : Nat.card ↥M = 64) (hB : Nat.card ↥B = 64)
    (hC : Nat.card ↥C = 64) (hTB : T ≤ B) (hTC : T ≤ C) (hTM : T ⊔ M = ⊤)
    (h8 : 8 ≤ Nat.card ↥(T ⊓ M)) : B = C := by
  have h := y63_card_mul_of_sup hTM
  rw [hG, hM] at h
  have hT : 64 ≤ Nat.card ↥T := by omega
  have h1 : T = B := Subgroup.eq_of_le_of_card_ge hTB (by omega)
  have h2 : T = C := Subgroup.eq_of_le_of_card_ge hTC (by omega)
  rw [← h1, ← h2]

end CFSG.OddStandard.HigherRank.YamadaG23
