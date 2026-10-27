module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneFinkelsteinNonabelianFour
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.SeitzReduction.RankOne

open CFSG.ComponentClassification.GMS78
open CFSG.ComponentClassification.GMS78.Finkelstein
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

theorem Finkelstein.Hyp.special_of_not_comm {U : Type} [Group U] [Finite U] {n : ℕ}
    {t y : MulAut U} (h : Finkelstein.Hyp U n t y) (hnc : ∃ a b : U, a * b ≠ b * a) :
    (∀ u v : U, ⁅u, v⁆ ∈ fixSubgroup t) ∧ (∀ u : U, u ^ 2 ∈ fixSubgroup t) ∧
      Nat.card U = 2 ^ (3 * n) := by
  suffices H : ∀ N : ℕ, ∀ (V : Type) [Group V] [Finite V] (t y : MulAut V),
      Finkelstein.Hyp V n t y → Nat.card V = N → (∃ a b : V, a * b ≠ b * a) →
      (∀ u v : V, ⁅u, v⁆ ∈ fixSubgroup t) ∧ (∀ u : V, u ^ 2 ∈ fixSubgroup t) ∧
        Nat.card V = 2 ^ (3 * n) from H _ U t y h rfl hnc
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro V _ _ t y h hN hnc
    by_cases hcomm : ∀ u v : V, ⁅u, v⁆ ∈ fixSubgroup t
    · exact ⟨hcomm, h.quot_elem_of_classTwo hcomm hnc⟩
    exfalso
    push Not at hcomm
    have hA := Finkelstein.Hyp.fix_ne_top_of_commutator hcomm
    have := h.fix_normal
    have hV := h.quot hA
    obtain ⟨u, v, huv⟩ := hcomm
    have hncV : ∃ a b : V ⧸ fixSubgroup t, a * b ≠ b * a := by
      refine ⟨u, v, fun hc => huv ?_⟩
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact hc
    have hlt : Nat.card (V ⧸ fixSubgroup t) < N := by
      rw [← hN, h.natCard_eq_quot_mul]
      have h1 : 0 < Nat.card (V ⧸ fixSubgroup t) := Nat.card_pos
      have h2 : 1 < 2 ^ n := Nat.one_lt_two_pow (by have := h.two_le; omega)
      nlinarith
    obtain ⟨-, hsqV, -⟩ := ih _ hlt _ _ _ hV rfl hncV
    have hsqB : ∀ w : V, w ^ 2 ∈ h.bSub := fun w => by
      have h1 := hsqV (w : V ⧸ fixSubgroup t)
      rw [← QuotientGroup.mk_pow] at h1
      exact (h.quot_mk_mem_fix_iff _).mp h1
    exact h.false_of_four hsqB ⟨u, v, huv⟩

end CFSG.SeitzReduction.RankOne
