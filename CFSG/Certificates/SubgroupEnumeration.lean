module

public import Mathlib.Algebra.Group.Subgroup.Pointwise

public section

namespace CFSG.Certificates.SubgroupEnumeration

variable {G : Type*} [Group G]

@[expose] def signedGenerators (A : Set G) : Set G :=
  A ∪ {x | ∃ a ∈ A, a⁻¹ = x}

@[expose] def WordWitness (A : Set G) (x : G) : Prop :=
  ∃ w : List G, (∀ a ∈ w, a ∈ signedGenerators A) ∧ w.prod = x

theorem signedGenerators_subset_closure (A : Set G) :
    signedGenerators A ⊆ (Subgroup.closure A : Set G) := by
  rintro x (hx | ⟨a, ha, rfl⟩)
  · exact Subgroup.subset_closure hx
  · exact (Subgroup.closure A).inv_mem (Subgroup.subset_closure ha)

theorem WordWitness.mem_closure {A : Set G} {x : G} (hx : WordWitness A x) :
    x ∈ Subgroup.closure A := by
  obtain ⟨w, hw, rfl⟩ := hx
  induction w with
  | nil => exact (Subgroup.closure A).one_mem
  | cons a w ih =>
    apply (Subgroup.closure A).mul_mem
    · exact signedGenerators_subset_closure A (hw a (by simp))
    · exact ih fun b hb => hw b (by simp [hb])

theorem wordWitness_of_mem_closure {A : Set G} {x : G} (hx : x ∈ Subgroup.closure A) :
    WordWitness A x := by
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨[], by simp, by simp⟩
  | mul_left a ha y _ ih =>
    obtain ⟨w, hw, rfl⟩ := ih
    refine ⟨a :: w, ?_, by simp⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Or.inl ha
    · exact hw b hb
  | inv_mul_cancel a ha y _ ih =>
    obtain ⟨w, hw, rfl⟩ := ih
    refine ⟨a⁻¹ :: w, ?_, by simp⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact Or.inr ⟨a, ha, rfl⟩
    · exact hw b hb

theorem wordWitness_iff_mem_closure (A : Set G) (x : G) :
    WordWitness A x ↔ x ∈ Subgroup.closure A :=
  ⟨WordWitness.mem_closure, wordWitness_of_mem_closure⟩

theorem WordWitness.mem_of_left_transitions {A E : Set G} {x : G}
    (hx : WordWitness A x) (h1 : (1 : G) ∈ E)
    (hleft : ∀ a ∈ signedGenerators A, ∀ e ∈ E, a * e ∈ E) : x ∈ E := by
  obtain ⟨w, hw, rfl⟩ := hx
  induction w with
  | nil => simpa using h1
  | cons a w ih =>
    have ha : a ∈ signedGenerators A := hw a (by simp)
    have hw' : ∀ b ∈ w, b ∈ signedGenerators A := fun b hb => hw b (by simp [hb])
    simpa using hleft a ha w.prod (ih hw')

end SubgroupEnumeration

open SubgroupEnumeration

variable {G : Type*} [Group G]

theorem subgroup_enumeration_completeness (A E : Set G) (h1 : (1 : G) ∈ E)
    (hwords : ∀ e ∈ E, WordWitness A e)
    (hleft : ∀ a ∈ signedGenerators A, ∀ e ∈ E, a * e ∈ E) :
    E = (Subgroup.closure A : Set G) := by
  apply Set.Subset.antisymm
  · intro e he
    exact (hwords e he).mem_closure
  · intro e he
    exact (wordWitness_of_mem_closure he).mem_of_left_transitions h1 hleft

theorem subgroup_enumeration_completeness_of_transitions (A E : Set G)
    (h1 : (1 : G) ∈ E) (hwords : ∀ e ∈ E, WordWitness A e)
    (hleft : ∀ a ∈ A, ∀ e ∈ E, a * e ∈ E)
    (hinverse : ∀ a ∈ A, ∀ e ∈ E, a⁻¹ * e ∈ E) :
    E = (Subgroup.closure A : Set G) := by
  apply subgroup_enumeration_completeness A E h1 hwords
  rintro a (ha | ⟨u, hu, rfl⟩) e he
  · exact hleft a ha e he
  · exact hinverse u hu e he

end CFSG.Certificates
