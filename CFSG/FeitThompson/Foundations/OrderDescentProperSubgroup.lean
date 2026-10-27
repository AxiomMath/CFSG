module

public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
import Mathlib.Algebra.Order.Ring.Abs

open Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G]

theorem natCard_lt_natCard_of_ne_top [Finite G] {H : Subgroup G} (hH : H ≠ ⊤) :
    Nat.card H < Nat.card G := by
  have hindex : 1 < H.index := Subgroup.one_lt_index_of_ne_top hH
  calc Nat.card H = 1 * Nat.card H := (one_mul _).symm
    _ < H.index * Nat.card H := Nat.mul_lt_mul_of_lt_of_le hindex le_rfl Nat.card_pos
    _ = Nat.card (Set.range fun g : G => g • (H : Set G)) * Nat.card H := by
        rw [natCard_range_leftCoset]
    _ = Nat.card G := (natCard_eq_natCard_range_leftCoset_mul_natCard H).symm

theorem natCard_lt_natCard_of_lt_top [Finite G] {H : Subgroup G} (hH : H < ⊤) :
    Nat.card H < Nat.card G :=
  natCard_lt_natCard_of_ne_top hH.ne

theorem natCard_lt_natCard_of_lt {H K : Subgroup G} [Finite K] (h : H < K) :
    Nat.card H < Nat.card K :=
  lt_of_le_of_ne (Subgroup.card_le_of_le h.le) fun he =>
    h.ne (Subgroup.eq_of_le_of_card_ge h.le he.ge)

theorem odd_natCard_subgroup (hG : Odd (Nat.card G)) (H : Subgroup G) : Odd (Nat.card H) :=
  hG.of_dvd_nat H.card_subgroup_dvd_card

theorem odd_natCard_lt_natCard_of_ne_top [Finite G] (hG : Odd (Nat.card G)) {H : Subgroup G}
    (hH : H ≠ ⊤) : Nat.card H < Nat.card G ∧ Odd (Nat.card H) :=
  ⟨natCard_lt_natCard_of_ne_top hH, odd_natCard_subgroup hG H⟩

end

end CFSG.FeitThompson
