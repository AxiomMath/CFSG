module

public import CFSG.ClassicalInvolution.Q3.TL4OddDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped commutatorElement

section Gen

variable {Q : Type} [Group Q] [Finite Q]

theorem commute_of_mem_normal_isPGroup {L : Subgroup Q} (hL : CFSG.IsComponent L)
    {P : Subgroup Q} (hPn : P.Normal) (hP2 : IsPGroup 2 P) {x : Q} (hx : x ∈ P) :
    ∀ y ∈ L, x * y = y * x := by
  rcases CFSG.LocalCores.component_normal_subgroup hL hPn with h | h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hL2 : IsPGroup 2 L := hP2.to_le h
    have hsolv : Group.IsSolvable L := by
      have := hL2.isNilpotent
      infer_instance
    have hnt : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial L).ne hL.1.1.commutator_eq_top
  · intro y hy
    have hc := Subgroup.commutator_mem_commutator hy hx
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc.symm

end Gen

theorem secMovedOddFree_of_inO2 {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {u : Y}
    {x : SecQ R u} (h : TightInO2 x) : SecMovedOddFree R u x := by
  obtain ⟨P, hPn, hP2, hxP⟩ := h
  intro L hL _ hmv
  exfalso
  obtain ⟨y, hy, hne⟩ := hmv
  exact hne (commute_of_mem_normal_isPGroup hL hPn hP2 hxP y hy)

end CFSG.ClassicalInvolution.Q3.TL4
