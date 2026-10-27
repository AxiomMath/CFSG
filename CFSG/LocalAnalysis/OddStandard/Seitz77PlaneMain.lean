module

public import CFSG.LocalAnalysis.OddStandard.Seitz77PlaneCent
public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionUnitary

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools Equiv

section Main

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ W : Subgroup G}

theorem Hyp.normalizer_adj_le (h : Hyp G A) (d : Datum A) (hR : Radicals d.V V₁ V₂)
    (hW : W = V₁ ∨ W = V₂) :
    normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) ≤ normalizer (W : Set G) :=
  h.facts.normalizer_adj_le d hR (alpha_of_certificates h d) hW

theorem Hyp.isConj_iff_mem_coset (h : Hyp G A) (d : Datum A) (hR : Radicals d.V V₁ V₂)
    (hW : W = V₁ ∨ W = V₂) {x : G} (hx : x ∈ W ⊔ zpowers d.t) :
    IsConj d.t x ↔ ∃ w ∈ W, x = d.t * w := by
  have := h.facts.mem_pts_iff d hR (alpha_of_certificates h d) hW (x := x)
  exact ⟨fun hc => this.mp ⟨hx, hc⟩, fun hw => (this.mpr hw).2⟩

theorem Hyp.exists_regularNormal_sylow_oddComplement
    (h : Hyp G A) (d : Datum A) (hR : Radicals d.V V₁ V₂) (hW : W = V₁ ∨ W = V₂)
    (hcent : ∀ x ∈ normalizer (A : Set G), (∀ w ∈ W, x * w = w * x) →
      x ∈ W ⊔ centralizer (A : Set G)) :
    ∃ X Q O : Subgroup G, IsRegularNormal (W ⊔ zpowers d.t : Subgroup G) d.t X ∧
      IsSylowOf 2 Q X ∧ (W ⊔ zpowers d.t : Subgroup G) < Q ∧ Odd (Nat.card O) ∧
      (∀ n ∈ normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G), ∀ o ∈ O, n * o * n⁻¹ ∈ O) ∧
      O ⊔ (W ⊔ zpowers d.t : Subgroup G) = centralizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) ∧
      Q ⊔ O = X ∧ Q ⊓ O = ⊥ :=
  h.facts.exists_regularNormal_sylow_oddComplement d hR (alpha_of_certificates h d) hW
    (h.aSide d hR hW) hcent

end Main

end CFSG.OddStandard.Seitz77
