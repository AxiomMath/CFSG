module

public import CFSG.Mathlib.GroupTheory.Basic
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneAbelianSubgroups
public import CFSG.Dihedral.DisconnectedInvolutionGraph.CyclicPSubgroupOrder

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem rank_one_two_center_lt_zpowers (hpgroup : IsPGroup 2 G)
    (hrank : NoCommutingDistinctInvolutions G) (element : G)
    (hnoncentral : element ∉ Subgroup.center G) :
    Subgroup.center G < Subgroup.zpowers element := by
  let generators : Set G := insert element (Subgroup.center G : Set G)
  let combined := Subgroup.closure generators
  have hcommuteGenerators : ∀ first ∈ generators, ∀ second ∈ generators, first * second = second * first := by
    intro first hfirst second hsecond
    rcases hfirst with rfl | hfirst
    · rcases hsecond with rfl | hsecond
      · rfl
      · exact Subgroup.mem_center_iff.mp hsecond first
    · rcases hsecond with rfl | hsecond
      · exact (Subgroup.mem_center_iff.mp hfirst second).symm
      · exact Subgroup.mem_center_iff.mp hsecond first
  let _ : IsMulCommutative combined := CFSG.subgroup_isMulCommutative_closure hcommuteGenerators
  have hcyclic : IsCyclic combined := rank_one_two_abelian_subgroup_cyclic hpgroup hrank
    combined (fun first second => mul_comm' first second)
  let _ := hcyclic
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have helementLe : Subgroup.zpowers element ≤ combined :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert _ _))
  have hcenterLe : Subgroup.center G ≤ combined := by
    intro other hmem
    exact Subgroup.subset_closure (Set.mem_insert_of_mem element hmem)
  have hcomparable := cyclic_pgroup_subgroups_comparable 2 (hpgroup.to_subgroup combined)
    ((Subgroup.center G).subgroupOf combined) ((Subgroup.zpowers element).subgroupOf combined)
  have hle : Subgroup.center G ≤ Subgroup.zpowers element := by
    rcases hcomparable with hle | hle
    · intro other hmem
      exact hle (show (⟨other, hcenterLe hmem⟩ : combined) ∈
        (Subgroup.center G).subgroupOf combined from hmem)
    · exfalso
      apply hnoncentral
      exact hle (show (⟨element, helementLe (Subgroup.mem_zpowers element)⟩ : combined) ∈
        (Subgroup.zpowers element).subgroupOf combined from Subgroup.mem_zpowers element)
  apply lt_of_le_of_ne hle
  intro heq
  apply hnoncentral
  rw [heq]
  exact Subgroup.mem_zpowers element

theorem rank_one_two_center_card_lt_order (hpgroup : IsPGroup 2 G)
    (hrank : NoCommutingDistinctInvolutions G) (element : G)
    (hnoncentral : element ∉ Subgroup.center G) :
    Nat.card (Subgroup.center G) < orderOf element := by
  have hstrict := rank_one_two_center_lt_zpowers hpgroup hrank element hnoncentral
  have hcardLe : Nat.card (Subgroup.center G) ≤ Nat.card (Subgroup.zpowers element) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hstrict.le)
  have hcardNe : Nat.card (Subgroup.center G) ≠ Nat.card (Subgroup.zpowers element) := by
    intro heq
    exact hstrict.ne (Subgroup.eq_of_le_of_card_ge hstrict.le heq.ge)
  rw [Nat.card_zpowers] at hcardLe hcardNe
  exact lt_of_le_of_ne hcardLe hcardNe

end CFSG.DisconnectedInvolutionGraph.Helpers
