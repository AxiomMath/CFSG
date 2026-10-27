module

public import CFSG.Mathlib.GroupTheory.Basic
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneAbelianSubgroups
public import CFSG.Dihedral.DisconnectedInvolutionGraph.CyclicPSubgroupOrder

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem rank_one_two_commuting_equal_order_zpowers (hpgroup : IsPGroup 2 G)
    (hrank : NoCommutingDistinctInvolutions G) (first second : G)
    (hcommute : first * second = second * first) (horder : orderOf first = orderOf second) :
    Subgroup.zpowers first = Subgroup.zpowers second := by
  let generators : Set G := {first, second}
  let combined := Subgroup.closure generators
  have hgeneratorsCommute : ∀ firstElement ∈ generators, ∀ secondElement ∈ generators,
      firstElement * secondElement = secondElement * firstElement := by
    intro firstElement hfirst secondElement hsecond
    rcases hfirst with rfl | hfirst
    · rcases hsecond with rfl | hsecond
      · rfl
      · rw [Set.mem_singleton_iff.mp hsecond]
        exact hcommute
    · rw [Set.mem_singleton_iff.mp hfirst]
      rcases hsecond with rfl | hsecond
      · exact hcommute.symm
      · rw [Set.mem_singleton_iff.mp hsecond]
  let _ : IsMulCommutative combined := CFSG.subgroup_isMulCommutative_closure hgeneratorsCommute
  let _ : IsCyclic combined := rank_one_two_abelian_subgroup_cyclic hpgroup hrank combined mul_comm'
  have hfirstLe : Subgroup.zpowers first ≤ combined :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert _ _))
  have hsecondLe : Subgroup.zpowers second ≤ combined :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hcard : Nat.card ((Subgroup.zpowers first).subgroupOf combined) =
      Nat.card ((Subgroup.zpowers second).subgroupOf combined) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hfirstLe).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsecondLe).toEquiv,
      Nat.card_zpowers, Nat.card_zpowers, horder]
  have heq : (Subgroup.zpowers first).subgroupOf combined =
      (Subgroup.zpowers second).subgroupOf combined := by
    apply le_antisymm
    · exact cyclic_subgroup_le_of_card_dvd _ _ (hcard ▸ dvd_rfl)
    · exact cyclic_subgroup_le_of_card_dvd _ _ (hcard.symm ▸ dvd_rfl)
  have hmapped := congrArg (fun subgroup : Subgroup combined => subgroup.map combined.subtype) heq
  rwa [Subgroup.map_subgroupOf_eq_of_le hfirstLe,
    Subgroup.map_subgroupOf_eq_of_le hsecondLe] at hmapped

end CFSG.DisconnectedInvolutionGraph.Helpers
