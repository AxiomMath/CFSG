module

public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

theorem u3_padic_card_eq_of_index_odd {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (h : ¬ 2 ∣ H.index) : padicValNat 2 (Nat.card H) = padicValNat 2 (Nat.card G) := by
  have hidx : padicValNat 2 H.index = 0 := padicValNat.eq_zero_of_not_dvd h
  have hcard : Nat.card H * H.index = Nat.card G := H.card_mul_index
  have hne : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hidx0 : H.index ≠ 0 := by
    intro h0
    apply h
    rw [h0]
    exact dvd_zero 2
  rw [← hcard, padicValNat.mul hne hidx0, hidx, add_zero]

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

end
