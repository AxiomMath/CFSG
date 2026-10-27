module

public import CFSG.GH74.Uniqueness.Setup

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Lemma46

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.not_zHull_le (S : ZDSetup X Z M) {H : Subgroup X} (hHM : ¬ H ≤ M)
    (hne : (Z ∩ ((H ⊓ M : Subgroup X) : Set X)).Nonempty) : ¬ zHull Z H ≤ M := by
  obtain ⟨z, hz, hzHM⟩ := hne
  have hzH : z ∈ H := (Subgroup.mem_inf.mp hzHM).1
  have hzL : z ∈ zHull Z H := Subgroup.subset_closure ⟨hz, hzH⟩
  intro hLM
  exact hHM ((le_normalizer_zHull S.invariant H).trans (S.prodDisc.normalizer_le hLM hz hzL))

theorem ZDSetup.exists_mem_zHull_not_mem (S : ZDSetup X Z M) {H : Subgroup X} (hHM : ¬ H ≤ M)
    (hne : (Z ∩ ((H ⊓ M : Subgroup X) : Set X)).Nonempty) : ∃ s ∈ Z, s ∈ H ∧ s ∉ M := by
  by_contra hall
  push Not at hall
  apply S.not_zHull_le hHM hne
  rw [zHull, Subgroup.closure_le]
  rintro x ⟨hxZ, hxH⟩
  exact hall x hxZ hxH

theorem ZDSetup.exists_conj_zHull (S : ZDSetup X Z M) {H : Subgroup X} (hHM : ¬ H ≤ M)
    (hne : (Z ∩ ((H ⊓ M : Subgroup X) : Set X)).Nonempty) {z₁ : X} (hz₁ : z₁ ∈ Z)
    (hz₁H : z₁ ∈ H) (hz₁M : z₁ ∈ M) {y : X} (hy : y ∈ Z) (hyH : y ∈ H) :
    ∃ l ∈ zHull Z H, l⁻¹ * z₁ * l = y := by
  have key : ∀ a ∈ Z, a ∈ H → a ∉ M → ∀ b ∈ Z, b ∈ H → b ∈ M →
      ∃ l ∈ zHull Z H, l⁻¹ * a * l = b := by
    intro a ha haH haM b hb hbH hbM
    obtain ⟨x, hxZ, hxcl, hx⟩ := S.prodDisc.exists_conj_mem_closure S.invariant ha haM hb
      (Or.inl hbM)
    refine ⟨x, ?_, hx⟩
    have hle : Subgroup.closure ({b, a} : Set X) ≤ zHull Z H := by
      rw [Subgroup.closure_le]
      rintro w (rfl | rfl)
      · exact Subgroup.subset_closure ⟨hb, hbH⟩
      · exact Subgroup.subset_closure ⟨ha, haH⟩
    exact hle hxcl
  obtain ⟨s, hsZ, hsH, hsM⟩ := S.exists_mem_zHull_not_mem hHM hne
  by_cases hyM : y ∈ M
  ·
    obtain ⟨l₁, hl₁, h₁⟩ := key s hsZ hsH hsM y hy hyH hyM
    obtain ⟨l₂, hl₂, h₂⟩ := key s hsZ hsH hsM z₁ hz₁ hz₁H hz₁M
    refine ⟨l₂⁻¹ * l₁, (zHull Z H).mul_mem ((zHull Z H).inv_mem hl₂) hl₁, ?_⟩
    rw [← h₁, ← h₂]
    group
  · obtain ⟨l, hl, h⟩ := key y hy hyH hyM z₁ hz₁ hz₁H hz₁M
    refine ⟨l⁻¹, (zHull Z H).inv_mem hl, ?_⟩
    rw [← h]
    group

end Lemma46

end CFSG.GH74.Uniqueness
