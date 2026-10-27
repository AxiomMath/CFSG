module

public import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
import CFSG.FeitThompson.Foundations.FiniteHomImageOrder
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex

open Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {X : Type*} [Group X] {π : Set ℕ} {H C : Subgroup X}

theorem isHallPiSubgroup_top_iff :
    IsHallPiSubgroup π (⊤ : Subgroup X) ↔ IsPiSubgroup π (⊤ : Subgroup X) :=
  ⟨fun h => h.isPiSubgroup, fun h => .top h⟩

theorem natCard_inf_subgroupOf (H C : Subgroup X) :
    Nat.card ((H ⊓ C).subgroupOf C) = Nat.card (H ⊓ C : Subgroup X) :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv

theorem index_inf_subgroupOf (H C : Subgroup X) :
    ((H ⊓ C).subgroupOf C).index = H.relIndex C := by
  rw [Subgroup.inf_subgroupOf_right]; rfl

theorem natCard_range_leftCoset_inf_subgroupOf (H C : Subgroup X) :
    Nat.card (Set.range fun g : C => g • (((H ⊓ C).subgroupOf C) : Set C)) = H.relIndex C := by
  rw [natCard_range_leftCoset, index_inf_subgroupOf]

theorem normal_inf_subgroupOf (hH : H.Normal) (C : Subgroup X) :
    ((H ⊓ C).subgroupOf C).Normal := by
  rw [Subgroup.inf_subgroupOf_right]; exact hH.subgroupOf C

theorem ker_quotientMk_comp_subtype (H C : Subgroup X) [H.Normal] :
    ((QuotientGroup.mk' H).comp C.subtype).ker = (H ⊓ C).subgroupOf C := by
  rw [Subgroup.inf_subgroupOf_right]
  ext g
  simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]

theorem index_inf_subgroupOf_eq_natCard_range (H C : Subgroup X) [H.Normal] :
    ((H ⊓ C).subgroupOf C).index = Nat.card ((QuotientGroup.mk' H).comp C.subtype).range := by
  rw [← ker_quotientMk_comp_subtype H C, Subgroup.index_ker]

theorem index_inf_subgroupOf_dvd_index [Finite X] (H C : Subgroup X) [H.Normal] :
    ((H ⊓ C).subgroupOf C).index ∣ H.index := by
  rw [index_inf_subgroupOf_eq_natCard_range, Subgroup.index_eq_card]
  exact natCard_range_dvd_natCard_codomain _

theorem IsHallPiSubgroup.isPiSubgroup_inf_subgroupOf [Finite X] (hHall : IsHallPiSubgroup π H)
    (C : Subgroup X) : IsPiSubgroup π ((H ⊓ C).subgroupOf C) :=
  isPiSubgroup_iff.2 fun p hp =>
    isPiSubgroup_iff.1 hHall.1 p (Nat.primeFactors_mono
      (by rw [natCard_inf_subgroupOf]; exact Subgroup.card_dvd_of_le inf_le_left)
      Nat.card_pos.ne' hp)

theorem IsHallPiSubgroup.notMem_of_mem_primeFactors_index_inf_subgroupOf [Finite X] (hH : H.Normal)
    (hHall : IsHallPiSubgroup π H) (C : Subgroup X) {p : ℕ}
    (hp : p ∈ ((H ⊓ C).subgroupOf C).index.primeFactors) : p ∉ π := by
  have : H.Normal := hH
  exact hHall.2 p (Nat.primeFactors_mono (index_inf_subgroupOf_dvd_index H C)
    Subgroup.index_ne_zero_of_finite hp)

theorem IsHallPiSubgroup.inf_subgroupOf [Finite X] (hH : H.Normal)
    (hHall : IsHallPiSubgroup π H) (C : Subgroup X) :
    IsHallPiSubgroup π ((H ⊓ C).subgroupOf C) :=
  ⟨hHall.isPiSubgroup_inf_subgroupOf C, fun _ hp =>
    hHall.notMem_of_mem_primeFactors_index_inf_subgroupOf hH C hp⟩

theorem IsHallPiSubgroup.normal_and_inf_subgroupOf [Finite X] (hH : H.Normal)
    (hHall : IsHallPiSubgroup π H) (C : Subgroup X) :
    ((H ⊓ C).subgroupOf C).Normal ∧ IsHallPiSubgroup π ((H ⊓ C).subgroupOf C) :=
  ⟨normal_inf_subgroupOf hH C, hHall.inf_subgroupOf hH C⟩

end

end CFSG.FeitThompson
