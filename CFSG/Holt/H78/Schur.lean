module

public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover

public section

namespace CFSG.Holt.H78

open Subgroup CFSG.LocalAnalysis.ComponentInitial

theorem isPerfect_of_ker_le_commutator {G A : Type*} [Group G] [Group A] [Group.IsPerfect A]
    (η : G →* A) (hη : Function.Surjective η) (hK : η.ker ≤ commutator G) :
    Group.IsPerfect G := by
  refine ⟨?_⟩
  have h := Subgroup.comap_map_eq η (commutator G)
  rw [CFSG.ComponentClassification.CentralExtensions.derived_map_eq_top η hη, Subgroup.comap_top,
    sup_eq_left.mpr hK] at h
  exact h.symm

theorem isPerfect_alternatingGroup {n : ℕ} (hn : 5 ≤ n) :
    Group.IsPerfect (alternatingGroup (Fin n)) :=
  ⟨commutator_alternatingGroup_eq_top (by simpa using hn)⟩

theorem card_ker_le_two_of_alternating_stem {G : Type*} [Group G] [Finite G] {n : ℕ}
    (hn : 5 ≤ n) (η : G →* alternatingGroup (Fin n)) (hη : Function.Surjective η)
    (hZ : η.ker ≤ center G) (hG : η.ker ≤ commutator G) (h2 : IsPGroup 2 η.ker) :
    Nat.card η.ker ≤ 2 := by
  have := isPerfect_alternatingGroup hn
  have : Group.IsPerfect G := isPerfect_of_ker_le_commutator η hη hG
  exact alternating_perfect_central_two_kernel_order_at_most_two hn η hη hZ h2

end CFSG.Holt.H78
