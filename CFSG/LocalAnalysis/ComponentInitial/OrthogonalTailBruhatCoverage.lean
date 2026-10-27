module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailBruhatExchange
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailBorelWeyl

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

theorem orthogonal_geometry_tail_Bruhat_coverage {K : Type*} [Field K] {A : Type*}
    [AddCommGroup A] [Module K A] [FiniteDimensional K A] {r : ℕ} {qA : QuadraticForm K A}
    (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0)
    (g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :
    g ∈ orthElementaryGroup (quadTail r qA) ↔
      ∃ b₁ ∈ tailBorel r qA, ∃ n ∈ tailTorusWeyl r qA a₀, ∃ b₂ ∈ tailBorel r qA,
        g = b₁ * n * b₂ := by
  refine ⟨fun hg => ?_, ?_⟩
  · rw [orthogonal_geometry_tail_Borel_Weyl_generation hani ha₀] at hg
    have hni : ∀ (i : Fin r) (y : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)),
        (∃ b₁ ∈ tailBorel r qA, ∃ n ∈ tailTorusWeyl r qA a₀, ∃ b₂ ∈ tailBorel r qA,
          y = b₁ * n * b₂) →
        ∃ b₁ ∈ tailBorel r qA, ∃ n ∈ tailTorusWeyl r qA a₀, ∃ b₂ ∈ tailBorel r qA,
          tailWeylElt r qA a₀ i * y = b₁ * n * b₂ := by
      rintro i _ ⟨b₁, h1, n, hn, b₂, h2, rfl⟩
      rcases (tailBorel_tailWeylElt_mul_mem hani ha₀ hn i (one_mem _) h1 h2).2 with
        ⟨c₁, hc₁, c₂, hc₂, he⟩ | ⟨c₁, hc₁, c₂, hc₂, he⟩
      · exact ⟨c₁, hc₁, _, mul_mem (tailWeylElt_mem_tailTorusWeyl a₀ i) hn, c₂, hc₂, by
          rw [← he]
          group⟩
      · exact ⟨c₁, hc₁, n, hn, c₂, hc₂, by
          rw [← he]
          group⟩
    induction hg using Subgroup.closure_induction_left with
    | one => exact ⟨1, one_mem _, 1, one_mem _, 1, one_mem _, by group⟩
    | mul_left x hx y _ ih =>
      rcases hx with hx | ⟨i, rfl⟩
      · obtain ⟨b₁, h1, n, hn, b₂, h2, rfl⟩ := ih
        exact ⟨x * b₁, mul_mem hx h1, n, hn, b₂, h2, by group⟩
      · exact hni i y ih
    | inv_mul_cancel x hx y _ ih =>
      rcases hx with hx | ⟨i, rfl⟩
      · obtain ⟨b₁, h1, n, hn, b₂, h2, rfl⟩ := ih
        exact ⟨x⁻¹ * b₁, mul_mem (inv_mem hx) h1, n, hn, b₂, h2, by group⟩
      ·
        have hsq := tailTorus_le_tailBorel (tailWeylElt_sq_mem_tailTorus hani ha₀ i)
        obtain ⟨b₁, h1, n, hn', b₂, h2, rfl⟩ := ih
        obtain ⟨c₁, hc₁, m, hm, c₂, hc₂, he⟩ := hni i
          ((tailWeylElt r qA a₀ i ^ 2)⁻¹ * b₁ * n * b₂)
          ⟨_, mul_mem (inv_mem hsq) h1, n, hn', b₂, h2, rfl⟩
        refine ⟨c₁, hc₁, m, hm, c₂, hc₂, ?_⟩
        rw [← he]
        group
  · rintro ⟨b₁, h1, n, hn, b₂, h2, rfl⟩
    exact mul_mem (mul_mem (tailBorel_le h1) (tailTorusWeyl_le a₀ hn)) (tailBorel_le h2)

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
