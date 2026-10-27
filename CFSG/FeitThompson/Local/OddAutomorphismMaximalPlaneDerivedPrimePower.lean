module

public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Local.HighRankMaximalPlaneCommutatorPrimePower
import CFSG.FeitThompson.Local.OddRankTwoAutomorphismDerivedPrimePower
import CFSG.FeitThompson.Local.SecondCenterPlaneCharacteristicCentralizer
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p n : ℕ} {R : Type*} [Group R]

theorem isPGroup_commutator_subgroup_of_odd_aut_of_isCyclic_or_maximal_plane [Finite R]
    (hp : p.Prime) (hodd : Odd p) (hRp : IsPGroup p R)
    (halt : IsCyclic R ∨
      ∃ E : Subgroup R, Maximal (IsElementaryAbelian p) E ∧ Nat.card E = p ^ 2)
    {B : Subgroup (MulAut R)} (hB : Odd (Nat.card B)) :
    IsPGroup p ↥(⁅B, B⁆ : Subgroup (MulAut R)) := by
  by_cases hrank : elementaryAbelianPRank p R ≤ 2
  · exact isPGroup_commutator_subgroup_of_odd_aut_of_elementaryAbelianPRank_le_two hp hodd hRp
      hrank hB
  · have hrank3 : 3 ≤ elementaryAbelianPRank p R := by omega
    rcases halt with hcyc | ⟨E, hE, hplane⟩
    · exact absurd hcyc (not_isCyclic_of_three_le_elementaryAbelianPRank hp hrank3)
    · exact isPGroup_commutator_of_maximal_plane hp hodd hRp
        (maximal_isElementaryAbelian_iff_maximal.1 hE) hplane hrank3 B

theorem isPGroup_commutator_of_odd_aut_of_isCyclic_or_maximal_plane [Finite R] (hp : p.Prime)
    (hodd : Odd p) (hRp : IsPGroup p R)
    (halt : IsCyclic R ∨
      ∃ E : Subgroup R, Maximal (IsElementaryAbelian p) E ∧ Nat.card E = p ^ 2)
    {B : Subgroup (MulAut R)} (hB : Odd (Nat.card B)) :
    IsPGroup p ↥(_root_.commutator ↥B) := by
  have h := isPGroup_commutator_subgroup_of_odd_aut_of_isCyclic_or_maximal_plane hp hodd hRp halt hB
  rw [← Subgroup.map_subtype_commutator] at h
  exact h.of_equiv
    ((_root_.commutator ↥B).equivMapOfInjective B.subtype B.subtype_injective).symm

theorem isPGroup_closure_setOf_inv_mul_inv_mul_mul_of_odd_aut_of_isCyclic_or_maximal_plane
    [Finite R] (hp : p.Prime) (hodd : Odd p) (hRp : IsPGroup p R)
    (halt : IsCyclic R ∨
      ∃ E : Subgroup R, Maximal (IsElementaryAbelian p) E ∧ Nat.card E = p ^ 2)
    {B : Subgroup (MulAut R)} (hB : Odd (Nat.card B)) :
    IsPGroup p ↥(Subgroup.closure {g : MulAut R | ∃ x ∈ B, ∃ y ∈ B, x⁻¹ * y⁻¹ * x * y = g}) := by
  rw [closure_setOf_inv_mul_inv_mul_mul]
  exact isPGroup_commutator_subgroup_of_odd_aut_of_isCyclic_or_maximal_plane hp hodd hRp halt hB

theorem exists_natCard_commutator_eq_pow_of_odd_aut_of_isCyclic_or_maximal_plane (hp : p.Prime)
    (hodd : Odd p) (hcard : Nat.card R = p ^ n)
    (halt : IsCyclic R ∨
      ∃ E : Subgroup R, Maximal (IsElementaryAbelian p) E ∧ Nat.card E = p ^ 2)
    {B : Subgroup (MulAut R)} (hB : Odd (Nat.card B)) :
    ∃ a : ℕ, Nat.card ↥(⁅B, B⁆ : Subgroup (MulAut R)) = p ^ a := by
  have := Fact.mk hp
  have : Finite R := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.pos.ne')
  exact IsPGroup.iff_card.1 (isPGroup_commutator_subgroup_of_odd_aut_of_isCyclic_or_maximal_plane
    hp hodd (IsPGroup.of_card hcard) halt hB)

end

end CFSG.FeitThompson
