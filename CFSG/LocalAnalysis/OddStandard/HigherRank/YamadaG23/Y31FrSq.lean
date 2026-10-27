module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAutFrame

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {Q : Type} [Group Q] [Finite Q] (fr : Frame (MulAut Q))

private lemma mem_S_of_mem_gens {fr : Frame (MulAut Q)} {x : MulAut Q}
    (hx : x ∈ ({fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀} : Set (MulAut Q))) : x ∈ fr.S := by
  change x ∈ Subgroup.closure ({fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀} : Set (MulAut Q))
  exact Subgroup.subset_closure hx

theorem frame_mem_Sσ_cases (h : fr.Fact11 (innerAut Q)) {α : MulAut Q} (hα : α ∈ fr.Sσ) :
    α ∈ fr.S ∨ ∃ s ∈ fr.S, α = s * fr.σ := by
  have hσ2 : fr.σ ^ 2 = 1 := frame_sigma_sq fr h
  have hσσ : fr.σ * fr.σ = 1 := by simpa [pow_two] using hσ2
  have hconj : ∀ y ∈ fr.S, fr.σ * y * fr.σ⁻¹ ∈ fr.S := by
    have hn := frame_sigma_normalizes fr h
    rw [Subgroup.mem_set_normalizer_iff] at hn
    intro y hy
    exact (hn y).mp hy
  rw [Frame.Sσ] at hα
  refine Subgroup.closure_induction (p := fun x _ => x ∈ fr.S ∨ ∃ s ∈ fr.S, x = s * fr.σ)
    ?mem ?one ?mul ?inv hα
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (mem_S_of_mem_gens (by simp))
    · exact Or.inl (mem_S_of_mem_gens (by simp))
    · exact Or.inl (mem_S_of_mem_gens (by simp))
    · exact Or.inl (mem_S_of_mem_gens (by simp))
    · exact Or.inl (mem_S_of_mem_gens (by simp))
    · exact Or.inr ⟨1, one_mem _, by rw [one_mul]⟩
  · exact Or.inl (one_mem _)
  · rintro x y _ _ (hxS | ⟨s, hs, rfl⟩) (hyS | ⟨s', hs', rfl⟩)
    · exact Or.inl (mul_mem hxS hyS)
    · refine Or.inr ⟨x * s', mul_mem hxS hs', ?_⟩
      group
    · refine Or.inr ⟨s * (fr.σ * y * fr.σ⁻¹), mul_mem hs (hconj y hyS), ?_⟩
      group
    · refine Or.inl ?_
      have hc : fr.σ * s' * fr.σ⁻¹ ∈ fr.S := hconj s' hs'
      have hkey : (s * fr.σ) * (s' * fr.σ) = s * (fr.σ * s' * fr.σ⁻¹) := by
        rw [show (s * fr.σ) * (s' * fr.σ) = s * (fr.σ * s' * fr.σ⁻¹) * (fr.σ * fr.σ) by
              group, hσσ, mul_one]
      rw [hkey]
      exact mul_mem hs hc
  · rintro x _ (hxS | ⟨s, hs, rfl⟩)
    · exact Or.inl (inv_mem hxS)
    · have hσinv : fr.σ⁻¹ = fr.σ := inv_eq_of_mul_eq_one_right hσσ
      refine Or.inr ⟨fr.σ * s⁻¹ * fr.σ⁻¹, hconj s⁻¹ (inv_mem hs), ?_⟩
      rw [mul_inv_rev, hσinv]
      rw [show fr.σ * s⁻¹ * fr.σ * fr.σ = fr.σ * s⁻¹ * (fr.σ * fr.σ) by group,
        hσσ, mul_one]

theorem frame_sq_mem_S (h : fr.Fact11 (innerAut Q)) {α : MulAut Q} (hα : α ∈ fr.Sσ) :
    α ^ 2 ∈ fr.S := by
  have hσ2 : fr.σ ^ 2 = 1 := frame_sigma_sq fr h
  have hσσ : fr.σ * fr.σ = 1 := by simpa [pow_two] using hσ2
  have hconj : ∀ y ∈ fr.S, fr.σ * y * fr.σ⁻¹ ∈ fr.S := by
    have hn := frame_sigma_normalizes fr h
    rw [Subgroup.mem_set_normalizer_iff] at hn
    intro y hy
    exact (hn y).mp hy
  rcases frame_mem_Sσ_cases fr h hα with hS | ⟨s, hs, rfl⟩
  · exact pow_mem hS 2
  · have hc : fr.σ * s * fr.σ⁻¹ ∈ fr.S := hconj s hs
    have hkey : (s * fr.σ) * (s * fr.σ) = s * (fr.σ * s * fr.σ⁻¹) := by
      rw [show (s * fr.σ) * (s * fr.σ) = s * (fr.σ * s * fr.σ⁻¹) * (fr.σ * fr.σ) by
            group, hσσ, mul_one]
    rw [pow_two, hkey]
    exact mul_mem hs hc

end CFSG.OddStandard.HigherRank.YamadaG23
