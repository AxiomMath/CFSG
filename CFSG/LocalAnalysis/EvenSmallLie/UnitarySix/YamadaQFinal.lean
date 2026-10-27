module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQFMain

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup

variable {G : Type*} [Group G]

namespace Hyp

variable [Finite G] {d : Data G} (h : Hyp d) (hB : HypB d) (hC : HypC d)
  (hV : ∀ v ∈ d.V₁, v * v = 1) (hQ : HypQ d)
include h hB hC hV hQ

theorem lemmaQ (hcase : HypNF d ∨ ∃ φ, HypF d φ) :
    d.D₁ ⊓ centralizer ({d.e} : Set G) ≤ normalizer (d.D₄ : Set G) ∧
      d.D₄ ≤ normalizer ((d.D₁ ⊓ centralizer ({d.e} : Set G) : Subgroup G) : Set G) ∧
      ⁅d.D₄, d.D₁ ⊓ centralizer ({d.e} : Set G)⁆ ≤ d.V₂ := by
  rcases hcase with hN | ⟨φ, hF⟩
  · exact h.lemmaQ_nf hB hC hV hQ hN
  · exact h.lemmaQ_f hF hB hC hV hQ

theorem yamada_4_16_3 (h4 : Hyp416 d) (hcase : HypNF d ∨ ∃ φ, HypF d φ) :
    d.D₂ ≤ normalizer (d.D₁ : Set G) ∧ d.D₁ ≤ normalizer (d.D₂ : Set G) :=
  ⟨h.D₂_le_normalizer_D₁ hB hC hV hQ h4 (h.lemmaQ hB hC hV hQ hcase),
    h.D₁_le_normalizer_D₂ hB hC hV hQ h4 (h.lemmaQ hB hC hV hQ hcase)⟩

theorem yamada_4_16_4 (h4 : Hyp416 d) (hcase : HypNF d ∨ ∃ φ, HypF d φ) :
    ⁅d.D₁ ⊔ d.D₂, d.D₁ ⊔ d.D₂⁆ = d.D₁ ⊓ d.D₂ ∧
      (d.D₁ ⊔ d.D₂) ⊓ centralizer ((d.D₁ ⊓ d.D₂ : Subgroup G) : Set G) = d.D₂ :=
  ⟨h.comm_sup_eq_inf hB hC hV hQ h4 (h.lemmaQ hB hC hV hQ hcase),
    h.sup_inf_cent_eq_D₂ hB hC hV hQ h4 (h.lemmaQ hB hC hV hQ hcase)⟩

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
