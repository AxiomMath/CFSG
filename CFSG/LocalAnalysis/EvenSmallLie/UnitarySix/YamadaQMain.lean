module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQNFMain
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQE

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaQ
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace Hyp

variable [Finite G] {d : Data G} (h : Hyp d)
include h

theorem exists_d₀ : ∃ d₀ ∈ d.D₄, d₀⁻¹ * d.t * d₀ * d.t = d.a₀ := by
  obtain ⟨y, hy, hyt⟩ := h.exists_D₄_conj h.a₀_mem
  exact ⟨y, hy, by rw [hyt, mul_assoc, h.t_sq, mul_one]⟩

theorem J_le_normalizer_V₂ : d.J ≤ normalizer (d.V₂ : Set G) := fun j hj =>
  mem_normalizer_sup (mem_normalizer_commutator (h.J_le_normalizer_D₄ hj) (le_normalizer hj))
    (by rw [h.J_eq] at hj; obtain ⟨k, rfl⟩ := hj; exact zpow_mem h.j₀_mem_normalizer_V₁ k)

omit [Finite G] h in
theorem comm_D₄_J_mem_V₂ : ∀ x ∈ d.D₄, ∀ j ∈ d.J, ⁅x, j⁆ ∈ d.V₂ := fun _ hx _ hj =>
  mem_sup_left (commutator_mem_commutator hx hj)

theorem E₁_le_normalizer_V₂ (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1) :
    d.D₁ ⊓ centralizer ({d.e} : Set G) ≤ normalizer (d.V₂ : Set G) := fun _ hu =>
  h.D₁_le_normalizer_of hB hC hV d.V₁_le_V₂ (h.V₂_le_D₁ hB hV) hu.1

theorem lemmaQ_nf (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1) (hQ : HypQ d)
    (hN : HypNF d) :
    d.D₁ ⊓ centralizer ({d.e} : Set G) ≤ normalizer (d.D₄ : Set G) ∧
      d.D₄ ≤ normalizer ((d.D₁ ⊓ centralizer ({d.e} : Set G) : Subgroup G) : Set G) ∧
      ⁅d.D₄, d.D₁ ⊓ centralizer ({d.e} : Set G)⁆ ≤ d.V₂ := by
  obtain ⟨d₀, hd₀, hθ⟩ := h.exists_d₀
  exact (h.configN_nf hB hC hV hQ hN hd₀ hθ).lemmaQ h.V₂_le_D₄ (h.V₂_le_E₁ hB hV)
    (h.E₁_le_normalizer_V₂ hB hC hV) h.J_le_normalizer_V₂ comm_D₄_J_mem_V₂
    (h.E₁_le_comm_sup hB hV hQ)

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
