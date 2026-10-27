module

public import Mathlib.GroupTheory.Index
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G H : Type*} [Group G] [Group H]

theorem coe_ker_eq_setOf (f : G →* H) : (f.ker : Set G) = {g : G | f g = 1} := by
  ext g
  simp [MonoidHom.mem_ker]

theorem natCard_setOf_map_eq_one (f : G →* H) :
    Nat.card {g : G | f g = 1} = Nat.card f.ker :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => MonoidHom.mem_ker.symm)

theorem natCard_setRange_eq_natCard_range (f : G →* H) :
    Nat.card (Set.range f) = Nat.card f.range :=
  Nat.card_congr (Equiv.subtypeEquivRight fun _ => f.mem_range.symm)

theorem natCard_range_mul_natCard_ker (f : G →* H) :
    Nat.card f.range * Nat.card f.ker = Nat.card G := by
  rw [natCard_eq_natCard_range_leftCoset_mul_natCard f.ker, natCard_range_leftCoset,
    Subgroup.index_ker]

theorem natCard_range_eq_natCard_div_natCard_ker [Finite G] (f : G →* H) :
    Nat.card f.range = Nat.card G / Nat.card f.ker := by
  rw [← natCard_range_mul_natCard_ker f, Nat.mul_div_cancel _ Nat.card_pos]

theorem natCard_setRange_eq_natCard_div_natCard_setOf [Finite G] (f : G →* H) :
    Nat.card (Set.range f) = Nat.card G / Nat.card {g : G | f g = 1} := by
  rw [natCard_setRange_eq_natCard_range, natCard_setOf_map_eq_one,
    natCard_range_eq_natCard_div_natCard_ker]

theorem natCard_setRange_dvd_natCard_domain (f : G →* H) :
    Nat.card (Set.range f) ∣ Nat.card G := by
  rw [natCard_setRange_eq_natCard_range]
  exact Subgroup.card_range_dvd f

theorem natCard_range_dvd_natCard_codomain [Finite H] (f : G →* H) :
    Nat.card f.range ∣ Nat.card H :=
  Subgroup.card_subgroup_dvd_card f.range

theorem natCard_setRange_dvd_natCard_codomain [Finite H] (f : G →* H) :
    Nat.card (Set.range f) ∣ Nat.card H := by
  rw [natCard_setRange_eq_natCard_range]
  exact natCard_range_dvd_natCard_codomain f

end

end CFSG.FeitThompson
