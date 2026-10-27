module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup
open scoped commutatorElement

theorem commutator_le_of_forall_commutator_mem {S : Type} [Group S] {C : Subgroup S} {s : S}
    (M : Subgroup S) [M.Normal] (hC : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a)
    (hcov : ∀ x : S, x ∈ C ∨ s⁻¹ * x ∈ C) (hM : ∀ c ∈ C, ⁅c, s⁆ ∈ M) :
    commutator S ≤ M := by
  set π : S →* S ⧸ M := QuotientGroup.mk' M with hπ
  have hs : ∀ c ∈ C, Commute (π s) (π c) := by
    intro c hc
    have h1 : π ⁅c, s⁆ = 1 := (QuotientGroup.eq_one_iff _).2 (hM c hc)
    rw [hπ, map_commutatorElement, commutatorElement_eq_one_iff_commute] at h1
    exact h1.symm
  have hCC : ∀ a ∈ C, ∀ b ∈ C, Commute (π a) (π b) := fun a ha b hb => by
    show π a * π b = π b * π a
    rw [← map_mul, ← map_mul, hC a ha b hb]
  have gen : ∀ x : S, ∃ c ∈ C, π x = π c ∨ π x = π s * π c := by
    intro x
    rcases hcov x with hx | hx
    · exact ⟨x, hx, Or.inl rfl⟩
    · exact ⟨s⁻¹ * x, hx, Or.inr (by rw [← map_mul, mul_inv_cancel_left])⟩
  have key : ∀ x y : S, Commute (π x) (π y) := by
    intro x y
    obtain ⟨c, hc, hx⟩ := gen x
    obtain ⟨c', hc', hy⟩ := gen y
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
    · exact hCC c hc c' hc'
    · exact (hs c hc).symm.mul_right (hCC c hc c' hc')
    · exact (hs c' hc').mul_left (hCC c hc c' hc')
    · exact ((Commute.refl _).mul_right (hs c' hc')).mul_left
        ((hs c hc).symm.mul_right (hCC c hc c' hc'))
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  refine (QuotientGroup.eq_one_iff _).1 ?_
  show π ⁅x, y⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
  exact key x y

end CFSG.EvenSporadicStandard.Induction.Junction
