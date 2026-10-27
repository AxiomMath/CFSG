module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.Assembly.Defs

public section

namespace CFSG.ComponentClassification.PerfectCyclicActions

theorem automorphisms_commutative (G : Type*) [Group G] [IsCyclic G] :
    IsMulCommutative (MulAut G) := by
  let equivalence := IsCyclic.mulAutMulEquiv G
  apply isMulCommutative_iff.mpr
  intro left right
  apply equivalence.injective
  rw [map_mul, map_mul, mul_comm]

theorem action_eq_one {G H : Type*} [Group G] [Group.IsPerfect G] [Group H] [IsCyclic H]
    (action : G →* MulAut H) : action = 1 := by
  let : IsMulCommutative (MulAut H) := automorphisms_commutative H
  exact PerfectAutomorphisms.hom_eq_one_of_commutative action

theorem normal_cyclic_le_derived_centralizer {G : Type*} [Group G]
    (subgroup : Subgroup G) [subgroup.Normal] [IsCyclic subgroup] :
    subgroup ≤ Subgroup.centralizer (commutator G : Set G) := by
  let action : G →* MulAut subgroup := MulAut.conjNormal
  let : IsMulCommutative (MulAut subgroup) := automorphisms_commutative subgroup
  have htrivial : (commutator G).map action = ⊥ := by
    have hderived := map_derivedSeries_le_derivedSeries action 1
    rw [derivedSeries_one, derivedSeries_one, commutator_eq_bot (MulAut subgroup)] at hderived
    exact le_antisymm hderived bot_le
  have hkernel := (Subgroup.map_eq_bot_iff _).mp htrivial
  intro element hmem
  apply Subgroup.mem_centralizer_iff.mpr
  intro other hother
  have haction : action other = 1 := MonoidHom.mem_ker.mp (hkernel hother)
  have hvalue := congrArg (fun automorphism : MulAut subgroup =>
    ((automorphism (⟨element, hmem⟩ : subgroup)) : G)) haction
  change other * element * other⁻¹ = element at hvalue
  calc
    other * element = (other * element * other⁻¹) * other := by group
    _ = element * other := by rw [hvalue]

theorem central_of_perfect {G : Type*} [Group G] [Group.IsPerfect G]
    (subgroup : Subgroup G) [subgroup.Normal] [IsCyclic subgroup] :
    subgroup ≤ Subgroup.center G := by
  have hcentralizes := normal_cyclic_le_derived_centralizer subgroup
  rw [Group.IsPerfect.commutator_eq_top] at hcentralizes
  intro element hmem
  apply Subgroup.mem_center_iff.mpr
  intro other
  exact Subgroup.mem_centralizer_iff.mp (hcentralizes hmem) other (Subgroup.mem_top other)

end CFSG.ComponentClassification.PerfectCyclicActions
