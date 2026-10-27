module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Setoid.Partition
public import Mathlib.Algebra.Group.Pointwise.Set.Card

open Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] (H : Subgroup G)

theorem setOf_leftRel_eq_leftCoset (y : G) :
    {x : G | QuotientGroup.leftRel H x y} = y • (H : Set G) := by
  ext x
  simp only [Set.mem_ofPred_eq, QuotientGroup.leftRel_apply, Set.mem_smul_set_iff_inv_smul_mem,
    SetLike.mem_coe, smul_eq_mul]
  exact ⟨fun hx => by simpa using H.inv_mem hx, fun hx => by simpa using H.inv_mem hx⟩

theorem range_leftCoset_eq_classes :
    (Set.range fun g : G => g • (H : Set G)) = (QuotientGroup.leftRel H).classes := by
  ext s
  simp only [Set.mem_range, Setoid.classes, Set.mem_ofPred_eq, setOf_leftRel_eq_leftCoset]
  exact ⟨fun ⟨g, hg⟩ => ⟨g, hg.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩

theorem isPartition_range_leftCoset :
    Setoid.IsPartition (Set.range fun g : G => g • (H : Set G)) := by
  rw [range_leftCoset_eq_classes]
  exact Setoid.isPartition_classes _

theorem pairwiseDisjoint_range_leftCoset :
    (Set.range fun g : G => g • (H : Set G)).PairwiseDisjoint id :=
  (isPartition_range_leftCoset H).pairwiseDisjoint

theorem natCard_range_leftCoset :
    Nat.card (Set.range fun g : G => g • (H : Set G)) = H.index := by
  rw [range_leftCoset_eq_classes, Subgroup.index_eq_card]
  exact (Nat.card_congr (Setoid.quotientEquivClasses _)).symm

theorem natCard_leftCoset (g : G) : Nat.card ↥(g • (H : Set G)) = Nat.card H :=
  Set.natCard_smul_set g _

theorem natCard_eq_natCard_range_leftCoset_mul_natCard :
    Nat.card G = Nat.card (Set.range fun g : G => g • (H : Set G)) * Nat.card H := by
  rw [natCard_range_leftCoset, Subgroup.index_mul_card]

end

end CFSG.FeitThompson
