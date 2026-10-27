module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.CoprimeSylow
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]

@[expose, instance_reducible]
def subgroupConjugationAction (subgroup : Subgroup G) : MulDistribMulAction subgroup G where
  smul actor element := (MulAut.conj actor.val) element
  one_smul element := by
    change 1 * element * (1 : G)⁻¹ = element
    simp only [one_mul, inv_one, mul_one]
  mul_smul first second element := by
    change (first.val * second.val) * element * (first.val * second.val)⁻¹ =
      first.val * (second.val * element * second.val⁻¹) * first.val⁻¹
    simp only [mul_inv_rev, mul_assoc]
  smul_mul actor first second := map_mul (MulAut.conj actor.val) first second
  smul_one actor := map_one (MulAut.conj actor.val)

theorem subgroup_conjugation_invariant_of_le_normalizer (subgroup actor : Subgroup G)
    (hle : actor ≤ Subgroup.normalizer (subgroup : Set G)) :
    let _ := subgroupConjugationAction actor
    InvariantSubgroup (A := actor) subgroup := by
  let _ := subgroupConjugationAction actor
  change InvariantSubgroup (A := actor) subgroup
  intro element other hmem
  exact (Subgroup.mem_normalizer_iff.mp (hle element.property) other).mp hmem

end CFSG.DisconnectedInvolutionGraph.Helpers
