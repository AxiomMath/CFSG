module

public import CFSG.GH74.Uniqueness.Section162Unitary

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.lemma162
    (S : ZDSetup X Z M) : Lemma162Stmt Z M := by
  intro c F hF hzF htF hy hFF
  obtain ⟨y, hyZ, hyF, hyM, hyz⟩ := hy
  have hFM : ¬ F ≤ M := fun h => c.htM (h htF)
  have hzFM : c.z ∈ Z ∩ ((F ⊓ M : Subgroup X) : Set X) := ⟨c.hz, mem_inf.mpr ⟨hzF, c.hzM⟩⟩
  have hyFM : y ∈ Z ∩ ((F ⊓ M : Subgroup X) : Set X) := ⟨hyZ, mem_inf.mpr ⟨hyF, hyM⟩⟩
  have hns := S.not_solvable_zHull_of_ne hF hFM hyFM hzFM hyz
  obtain ⟨n, i, e, hB⟩ := S.benderSub_exists hF hFM ⟨c.z, hzFM⟩ hns
  rw [hFF] at hB
  refine ⟨n, hB.bender.two_le.2, ?_⟩
  rcases hB.bender.cases' with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
  · left
    obtain ⟨h1, h2⟩ := S.fZero_eq_of_benderSub hB (Or.inl rfl) c.ht c.htM htF
    exact ⟨h1, Or.inl h2⟩
  · left
    obtain ⟨h1, h2⟩ := S.fZero_eq_of_benderSub hB (Or.inr rfl) c.ht c.htM htF
    exact ⟨h1, Or.inr h2⟩
  · right
    obtain ⟨h1, h2, h3⟩ := S.lemma162_unitary hB c.ht c.htM htF c.hz c.hzM hzF
    exact ⟨h1, ⟨e, hB⟩, h2, h3⟩

end CFSG.GH74.Uniqueness
