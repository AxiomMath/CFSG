module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.EvenSporadicStandard

theorem commutator_le_of_index_eq_two {Y : Type*} [Group Y] {N : Subgroup Y}
    (hN : N.index = 2) : commutator Y ≤ N := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hN,
    Subgroup.mul_mem_iff_of_index_two hN, Subgroup.mul_mem_iff_of_index_two hN, inv_mem_iff,
    inv_mem_iff]
  tauto

end CFSG.EvenSporadicStandard
