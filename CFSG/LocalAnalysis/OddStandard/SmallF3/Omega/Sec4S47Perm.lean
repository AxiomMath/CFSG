module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Equiv Equiv.Perm

private lemma exists_fixed_of_isThreeCycle {α : Type*} [Fintype α] [DecidableEq α]
    (hα : 3 ≤ Fintype.card α) {c : Perm (Option α)} (hc : c.IsThreeCycle) :
    ∃ q : Option α, c q = q := by
  by_contra h
  push Not at h
  have hsupp : c.support = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro q
    exact mem_support.mpr (h q)
  have hcard : c.support.card = 3 := hc.card_support
  rw [hsupp, Finset.card_univ, Fintype.card_option] at hcard
  omega

private lemma optionCongr_removeNone_of_fixed {α : Type*} [DecidableEq α]
    {σ : Perm (Option α)} (h : σ none = none) :
    Equiv.optionCongr (Equiv.removeNone σ) = σ := by
  rw [map_equiv_removeNone, h, Equiv.swap_self]
  exact Equiv.trans_refl σ

private lemma isThreeCycle_conj_inv {β : Type*} [Fintype β] [DecidableEq β]
    {c g : Perm β} (hc : c.IsThreeCycle) : (g⁻¹ * c * g).IsThreeCycle := by
  show (g⁻¹ * c * g).cycleType = {3}
  have h : (g⁻¹ * c * g).cycleType = c.cycleType := by
    simpa using cycleType_conj (σ := c) (τ := g⁻¹)
  rw [h, hc.cycleType]

theorem sec4S47_alt_le {α : Type*} [Fintype α] [DecidableEq α] (hα : 3 ≤ Fintype.card α)
    {R : Subgroup (Perm (Option α))} (htr : ∀ q : Option α, ∃ g ∈ R, g none = q)
    (hst : ∀ σ ∈ alternatingGroup α, Equiv.optionCongr σ ∈ R) :
    alternatingGroup (Option α) ≤ R := by
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
  refine (Subgroup.closure_le R).mpr ?_
  intro c hc
  obtain ⟨q, hq⟩ := exists_fixed_of_isThreeCycle hα hc
  obtain ⟨g, hgR, hgnone⟩ := htr q
  let c' : Perm (Option α) := g⁻¹ * c * g
  have hc'3 : c'.IsThreeCycle := isThreeCycle_conj_inv hc
  have hc'none : c' none = none := by
    have h1 : c' none = g⁻¹ (c (g none)) := by simp only [c', mul_apply]
    rw [h1, hgnone, hq, ← hgnone]
    simp
  have hcongr : Equiv.optionCongr (Equiv.removeNone c') = c' :=
    optionCongr_removeNone_of_fixed hc'none
  have hsign : Perm.sign (Equiv.removeNone c') = 1 := by
    rw [← Equiv.optionCongr_sign (Equiv.removeNone c'), hcongr, hc'3.sign]
  have hσmem : Equiv.removeNone c' ∈ alternatingGroup α :=
    Equiv.Perm.mem_alternatingGroup.mpr hsign
  have hc'R : c' ∈ R := by
    have h := hst (Equiv.removeNone c') hσmem
    rwa [hcongr] at h
  have hc_eq : c = g * c' * g⁻¹ := by
    simp only [c']
    group
  rw [hc_eq]
  exact R.mul_mem (R.mul_mem hgR hc'R) (R.inv_mem hgR)

end CFSG.OddStandard.SmallF3.Omega
