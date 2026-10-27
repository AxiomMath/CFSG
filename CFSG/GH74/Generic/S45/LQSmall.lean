module

public import CFSG.GH74.Generic.S45.LQData
public import CFSG.GH74.Generic.S45.LExcBase

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.Blueprint Subgroup CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.ExcSelector
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem QData.smallQ8 {S : Type} [Group S] {ya : MulAut S} {Lb : Subgroup S} {q : ℕ}
    (hQ : QData S ya Lb q) : SmallQ8 Lb := by
  refine ⟨?_, q, hQ.q5, hQ.mod8, hQ.card⟩
  obtain ⟨p, f, hp, hf, ⟨h5, hodd⟩, hmodel⟩ := hQ.model (fun x => 5 ≤ x ∧ Odd x) ⟨hQ.q5, hQ.odd⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have hZ : Subgroup.center ↥Lb = ⊥ := center_eq_bot_of_simple_nonab hQ.simple hQ.nonab
  have e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* ↥Lb :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine Or.inl ⟨p, f, hp, hp2, hf, h5, lieModel_psl_of_equiv e.symm hmodel, ?_⟩
  rw [hZ]
  have : Nat.card ↥(⊥ : Subgroup ↥Lb) = 1 := Subgroup.card_bot
  rw [this]
  exact odd_one

theorem QData.isComponentOf_fixed {S : Type} [Group S] {ya : MulAut S} {Lb : Subgroup S} {q : ℕ}
    (hQ : QData S ya Lb q) : CFSG.Assembly.IsComponentOf Lb (fixedSubgroup ya) := by
  have hFeq : fixedSubgroup ya = autFixed ya := by
    ext x
    exact Iff.rfl
  have hLb : Lb ≤ fixedSubgroup ya := by
    rw [hFeq]
    exact hQ.le
  rw [CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLb, hFeq]
  exact hQ.isComponent

end CFSG.GH74.Generic.S45
