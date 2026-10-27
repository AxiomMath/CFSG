module

public import CFSG.Assembly.Defs

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem disjoint_mutually_normalized_subgroups_centralize {G : Type u} [Group G]
    (first second : Subgroup G)
    (hfirstNormalizes : first ≤ Subgroup.normalizer (second : Set G))
    (hsecondNormalizes : second ≤ Subgroup.normalizer (first : Set G))
    (hdisjoint : Disjoint first second) :
    first ≤ Subgroup.centralizer (second : Set G) := by
  intro firstMember hfirst
  apply Subgroup.mem_centralizer_iff.mpr
  intro secondMember hsecond
  have hfirstCommutator : ⁅firstMember, secondMember⁆ ∈ first := by
    rw [commutatorElement_def]
    have hconjugate := Subgroup.le_normalizer_iff.mp hsecondNormalizes secondMember hsecond
      firstMember⁻¹ (first.inv_mem hfirst)
    convert first.mul_mem hfirst hconjugate using 1
    group
  have hsecondCommutator : ⁅firstMember, secondMember⁆ ∈ second := by
    rw [commutatorElement_def]
    exact second.mul_mem (Subgroup.le_normalizer_iff.mp hfirstNormalizes firstMember hfirst secondMember hsecond)
      (second.inv_mem hsecond)
  exact (commutatorElement_eq_one_iff_mul_comm.mp
    (Subgroup.disjoint_def.mp hdisjoint hfirstCommutator hsecondCommutator)).symm

end CFSG.RankThreeEvenClassification.Helpers
