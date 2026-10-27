module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

theorem exists_gen_map_conj {S : Type} [Group S] {Y : Subgroup S} (hY : Nat.card Y = 3)
    (g : S) :
    ∃ a : S, orderOf a = 3 ∧ Y.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers a := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hcardH : Nat.card ↥(Y.map (MulAut.conj g).toMonoidHom) = 3 := by
    rw [← hY]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective Y _ hinj).toEquiv).symm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic ↥(Y.map (MulAut.conj g).toMonoidHom) := isCyclic_of_prime_card hcardH
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := ↥(Y.map (MulAut.conj g).toMonoidHom))
  refine ⟨(x : S), ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hx, hcardH]
  · apply le_antisymm
    · intro y hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hx ⟨y, hy⟩)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have h2 : (x : S) ^ k = ((x ^ k : ↥(Y.map (MulAut.conj g).toMonoidHom)) : S) := rfl
      exact h2.trans (congrArg Subtype.val hk)
    · exact Subgroup.zpowers_le.mpr x.2

end CFSG.HardMathSupport.RichardWeiss.Proving

end
