module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem conj_mem_commutator {f : G} {E : Subgroup G} (hf : ∀ e ∈ E, f * e * f⁻¹ ∈ E) :
    ∀ g ∈ ⁅zpowers f, E⁆, f * g * f⁻¹ ∈ ⁅zpowers f, E⁆ := by
  intro g hg
  have hle : ⁅zpowers f, E⁆ ≤ (⁅zpowers f, E⁆).comap (MulAut.conj f).toMonoidHom := by
    rw [commutator_le]
    intro a ha b hb
    show f * ⁅a, b⁆ * f⁻¹ ∈ ⁅zpowers f, E⁆
    have hcomm : f * a = a * f := by
      obtain ⟨k, rfl⟩ := ha
      exact ((Commute.refl f).zpow_right k).eq
    have e1 : f * a * f⁻¹ = a := by rw [hcomm]; group
    have e2 : f * ⁅a, b⁆ * f⁻¹ = ⁅a, f * b * f⁻¹⁆ := by
      have : f * ⁅a, b⁆ * f⁻¹ = ⁅f * a * f⁻¹, f * b * f⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [this, e1]
    rw [e2]
    exact commutator_mem_commutator ha (hf b hb)
  exact hle hg

theorem mem_normalizer_commutator {f : G} {E : Subgroup G} (hf : f ∈ normalizer (E : Set G)) :
    f ∈ normalizer ((⁅zpowers f, E⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  have hf1 : ∀ e ∈ E, f * e * f⁻¹ ∈ E := fun e he => (mem_normalizer_iff.1 hf e).1 he
  have hf2 : ∀ e ∈ E, f⁻¹ * e * f⁻¹⁻¹ ∈ E := by
    intro e he
    have h2 := (mem_normalizer_iff.1 hf (f⁻¹ * e * f⁻¹⁻¹)).2
    have e3 : f * (f⁻¹ * e * f⁻¹⁻¹) * f⁻¹ = e := by group
    rw [e3] at h2
    exact h2 he
  constructor
  · exact fun hg => conj_mem_commutator hf1 g hg
  · intro h
    have h3 := conj_mem_commutator (f := f⁻¹) (E := E) hf2
    rw [zpowers_inv] at h3
    have := h3 _ h
    have e4 : f⁻¹ * (f * g * f⁻¹) * f⁻¹⁻¹ = g := by group
    rwa [e4] at this

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
