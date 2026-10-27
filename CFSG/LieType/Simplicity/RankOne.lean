module

public import CFSG.LieType.TitsSimplicity.Simplicity

public section

namespace CFSG.LieType.Simplicity

open CFSG.LieType.TitsSimplicity

variable {Γ : Type*} [Group Γ]

theorem eq_top_of_le_of_not_le {B P : Subgroup Γ} {n : Γ}
    (hbruhat : ∀ g, g ∈ B ∨ ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * n * b₂) (hBP : B ≤ P)
    (hP : ¬ P ≤ B) : P = ⊤ := by
  obtain ⟨g, hgP, hgB⟩ := Set.not_subset.1 hP
  rcases hbruhat g with h | ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  · exact absurd h hgB
  · have hn : n ∈ P := by
      have e : n = b₁⁻¹ * (b₁ * n * b₂) * b₂⁻¹ := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem (hBP hb₁)) hgP) (inv_mem (hBP hb₂))
    rw [eq_top_iff]
    intro x _
    rcases hbruhat x with h | ⟨c₁, hc₁, c₂, hc₂, rfl⟩
    · exact hBP h
    · exact mul_mem (mul_mem (hBP hc₁) hn) (hBP hc₂)

theorem le_normalCore_or_eq_top_of_rankOne {B : Subgroup Γ} {n : Γ}
    (hbruhat : ∀ g, g ∈ B ∨ ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * n * b₂) (hperf : Group.IsPerfect Γ)
    (hB : Group.IsSolvable B) (M : Subgroup Γ) [M.Normal] : M ≤ B.normalCore ∨ M = ⊤ := by
  by_cases hMB : M ≤ B
  · exact .inl (Subgroup.normal_le_normalCore.2 hMB)
  · exact .inr (eq_top_of_sup_eq_top hperf hB
      (eq_top_of_le_of_not_le hbruhat le_sup_right fun h => hMB (le_sup_left.trans h)))

theorem le_center_of_inf_eq_bot {B U C : Subgroup Γ} [hC : C.Normal] (hCB : C ≤ B)
    (hUB : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U) (hCU : C ⊓ U = ⊥)
    (hgen : Subgroup.normalClosure (U : Set Γ) = ⊤) : C ≤ Subgroup.center Γ := by
  have hcomm : ∀ c ∈ C, ∀ u ∈ U, c * u = u * c := by
    intro c hc u hu
    have h1 : c * u * c⁻¹ * u⁻¹ ∈ C := by
      have : u * c⁻¹ * u⁻¹ ∈ C := hC.conj_mem _ (inv_mem hc) u
      have e : c * u * c⁻¹ * u⁻¹ = c * (u * c⁻¹ * u⁻¹) := by group
      rw [e]
      exact mul_mem hc this
    have h2 : c * u * c⁻¹ * u⁻¹ ∈ U := mul_mem (hUB c (hCB hc) u hu) (inv_mem hu)
    have h3 : c * u * c⁻¹ * u⁻¹ = 1 := by
      have : c * u * c⁻¹ * u⁻¹ ∈ C ⊓ U := ⟨h1, h2⟩
      rw [hCU] at this
      exact this
    calc c * u = c * u * c⁻¹ * u⁻¹ * (u * c) := by group
      _ = u * c := by rw [h3, one_mul]
  have hconj : (U : Set Γ) ⊆ (Subgroup.centralizer (C : Set Γ) : Set Γ) := by
    intro u hu
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro c hc
    exact hcomm c hc u hu
  have hle : Subgroup.normalClosure (U : Set Γ) ≤ Subgroup.centralizer (C : Set Γ) :=
    Subgroup.normalClosure_le_normal hconj
  rw [hgen, top_le_iff] at hle
  intro c hc
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer (C : Set Γ) := hle ▸ Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.1 hg c hc).symm

theorem isSimpleGroup_quotient_center_of_rankOne [Nontrivial Γ] {B U : Subgroup Γ} {n : Γ}
    (hbruhat : ∀ g, g ∈ B ∨ ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * n * b₂) (hperf : Group.IsPerfect Γ)
    (hB : Group.IsSolvable B) (hUB : ∀ b ∈ B, ∀ u ∈ U, b * u * b⁻¹ ∈ U)
    (hCU : B.normalCore ⊓ U = ⊥) (hgen : Subgroup.normalClosure (U : Set Γ) = ⊤) :
    IsSimpleGroup (Γ ⧸ Subgroup.center Γ) := by
  have hcore : B.normalCore ≤ Subgroup.center Γ :=
    le_center_of_inf_eq_bot (Subgroup.normalCore_le B) hUB hCU hgen
  refine isSimpleGroup_quotient_center_of_forall hperf fun M hM => ?_
  rcases le_normalCore_or_eq_top_of_rankOne hbruhat hperf hB M with h | h
  · exact .inl (h.trans hcore)
  · exact .inr h

end CFSG.LieType.Simplicity
