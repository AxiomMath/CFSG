module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48TI

public section

namespace CFSG.HardMathSupport.Malle.OvergroupTransport

open Subgroup CFSG.AGLEmbedding.KFactProofs.Sp48

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem centralizer_le_of_proper_overgroup {N M₁ Z : Subgroup G} (hNM : N ≤ M₁) (hM₁ : M₁ ≠ ⊤)
    (hD : ∀ x ∈ Z, x ≠ 1 → ∀ H : Subgroup G, N ⊓ centralizer ({x} : Set G) ≤ H →
      H ≤ centralizer ({x} : Set G) →
        H = N ⊓ centralizer ({x} : Set G) ∨ H = centralizer ({x} : Set G))
    (hTr : ∀ x ∈ Z, x ≠ 1 → ∀ y ∈ Z, y ≠ 1 → ∃ n ∈ N, ∀ g : G,
      g ∈ centralizer ({y} : Set G) → n⁻¹ * g * n ∈ centralizer ({x} : Set G))
    (hGen : Subgroup.closure {k : G | ∃ x ∈ Z, x ≠ 1 ∧ k * x = x * k} = ⊤) :
    ∀ x ∈ Z, x ≠ 1 → M₁ ⊓ centralizer ({x} : Set G) ≤ N := by
  intro x hx hx1
  by_contra hne
  rcases hD x hx hx1 (M₁ ⊓ centralizer ({x} : Set G)) (inf_le_inf_right _ hNM) inf_le_right
    with h | h
  · exact hne (h ▸ inf_le_left)
  · have hCx : centralizer ({x} : Set G) ≤ M₁ := inf_eq_right.mp h
    have hall : ∀ y ∈ Z, y ≠ 1 → centralizer ({y} : Set G) ≤ M₁ := by
      intro y hy hy1 g hg
      obtain ⟨n, hn, hconj⟩ := hTr x hx hx1 y hy hy1
      have h1 : n⁻¹ * g * n ∈ M₁ := hCx (hconj g hg)
      have : g = n * (n⁻¹ * g * n) * n⁻¹ := by group
      rw [this]
      exact M₁.mul_mem (M₁.mul_mem (hNM hn) h1) (M₁.inv_mem (hNM hn))
    have hle : Subgroup.closure {k : G | ∃ x ∈ Z, x ≠ 1 ∧ k * x = x * k} ≤ M₁ := by
      rw [Subgroup.closure_le]
      rintro k ⟨y, hy, hy1, hk⟩
      refine hall y hy hy1 ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact hk.symm
    rw [hGen] at hle
    exact hM₁ (top_le_iff.mp hle)

end CFSG.HardMathSupport.Malle.OvergroupTransport
