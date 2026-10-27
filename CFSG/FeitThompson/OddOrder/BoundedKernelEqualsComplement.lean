module

public import Mathlib.Data.Int.ModEq
public import Mathlib.GroupTheory.Index
import CFSG.FeitThompson.OddOrder.CongruentProductSupportGap

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {H : Type*} [Group H] [Finite H] {U : Subgroup H}

theorem eq_top_of_modEq_one_of_ediv_le {m : ℤ} (hU : U ≠ ⊥) (hm : 2 ≤ m)
    (hh : (Nat.card H : ℤ) ≡ 1 [ZMOD m]) (hu : (Nat.card U : ℤ) ≡ 1 [ZMOD m])
    (hbound : ((Nat.card H : ℤ) - 1) / m ≤ m - 1) : U = ⊤ := by
  by_contra hne
  have hx : 1 < U.index := Subgroup.one_lt_index_of_ne_top hne
  have hu1 : 1 < Nat.card U := (Subgroup.one_lt_card_iff_ne_bot U).2 hU
  have hcard : (Nat.card H : ℤ) = (Nat.card U : ℤ) * (U.index : ℤ) := by
    rw [← Nat.cast_mul, U.card_mul_index]
  have := sub_one_lt_ediv_of_modEq_one hm (by exact_mod_cast hu1) (by exact_mod_cast hx) hcard hh hu
  omega

theorem natCard_eq_of_modEq_one_of_ediv_le {m : ℤ} (hU : U ≠ ⊥) (hm : 2 ≤ m)
    (hh : (Nat.card H : ℤ) ≡ 1 [ZMOD m]) (hu : (Nat.card U : ℤ) ≡ 1 [ZMOD m])
    (hbound : ((Nat.card H : ℤ) - 1) / m ≤ m - 1) : Nat.card U = Nat.card H := by
  rw [eq_top_of_modEq_one_of_ediv_le hU hm hh hu hbound, Nat.card_congr Subgroup.topEquiv.toEquiv]

theorem index_eq_one_of_modEq_one_of_ediv_le {m : ℤ} (hU : U ≠ ⊥) (hm : 2 ≤ m)
    (hh : (Nat.card H : ℤ) ≡ 1 [ZMOD m]) (hu : (Nat.card U : ℤ) ≡ 1 [ZMOD m])
    (hbound : ((Nat.card H : ℤ) - 1) / m ≤ m - 1) : U.index = 1 := by
  rw [eq_top_of_modEq_one_of_ediv_le hU hm hh hu hbound, Subgroup.index_top]

theorem eq_of_le_of_modEq_one_of_ediv_le {G : Type*} [Group G] {U K : Subgroup G} [Finite K]
    (hUK : U ≤ K) (hU : U ≠ ⊥) {m : ℤ} (hm : 2 ≤ m)
    (hh : (Nat.card K : ℤ) ≡ 1 [ZMOD m]) (hu : (Nat.card U : ℤ) ≡ 1 [ZMOD m])
    (hbound : ((Nat.card K : ℤ) - 1) / m ≤ m - 1) : U = K := by
  have hcard : Nat.card (U.subgroupOf K) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv
  have hbot : U.subgroupOf K ≠ ⊥ := fun h =>
    hU (Subgroup.eq_bot_of_card_eq _ (by rw [← hcard, h, Subgroup.card_bot]))
  refine le_antisymm hUK (Subgroup.subgroupOf_eq_top.1 ?_)
  exact eq_top_of_modEq_one_of_ediv_le hbot hm hh (by rwa [hcard]) hbound

end CFSG.FeitThompson
