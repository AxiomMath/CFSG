module

public import CFSG.LocalAnalysis.OddStandard.Seitz77V1Act
public import CFSG.LocalAnalysis.OddStandard.Seitz77PlaneMain
public import Certificates.Certificate5183
public import Certificates.Certificate6126
public import Certificates.Certificate6127

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification CFSG.PSL3Four
  CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

theorem centralizer_V₁_le_of_certificate
    {G : Type*} [Group G] [Finite G]
    {A V V₁ V₂ W : Subgroup G} (hA : commutator ↥A = ⊤) (hZ : Odd (Nat.card (center ↥A)))
    (e : ↥A ⧸ center ↥A ≃* ↥PSL3Four.S) (hV : IsSylowOf 2 V A) (hR : Radicals V V₁ V₂)
    (hW : W = V₁ ∨ W = V₂) :
    normalizer (A : Set G) ⊓ centralizer (W : Set G) ≤ W ⊔ centralizer (A : Set G) :=
  centralizer_V₁_le hA hZ e hV hR hW Certificates.certificate5183
    Certificates.certificate6126

theorem card_fixed_le_four_of_certificate
    {G : Type*} [Group G] [Finite G] {A V V₁ V₂ W : Subgroup G} (hA : commutator ↥A = ⊤)
    (hZ : Odd (Nat.card (center ↥A))) (e : ↥A ⧸ center ↥A ≃* ↥PSL3Four.S)
    (hV : IsSylowOf 2 V A) (hR : Radicals V V₁ V₂) (hW : W = V₁ ∨ W = V₂) :
    ∀ x ∈ normalizer (A : Set G) ⊓ normalizer (W : Set G), x ∉ W ⊔ centralizer (A : Set G) →
      Nat.card ↥(W ⊓ centralizer ({x} : Set G)) ≤ 4 :=
  card_fixed_le_four hA hZ e hV hR hW Certificates.certificate5183
    Certificates.certificate6126 Certificates.certificate6127

theorem relIndex_le_four_of_certificate
    {G : Type*} [Group G] [Finite G] {A V V₁ V₂ W : Subgroup G} (hA : commutator ↥A = ⊤)
    (hZ : Odd (Nat.card (center ↥A))) (e : ↥A ⧸ center ↥A ≃* ↥PSL3Four.S)
    (hV : IsSylowOf 2 V A) (hR : Radicals V V₁ V₂) (hW : W = V₁ ∨ W = V₂) :
    ∀ E : Subgroup G, E ≤ normalizer (A : Set G) ⊓ normalizer (W : Set G) →
      (∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ centralizer (W : Set G) ∧ x * x ∈ centralizer (W : Set G)) →
      (centralizer (W : Set G)).relIndex E ≤ 4 :=
  relIndex_le_four hA hZ e hV hR hW Certificates.certificate5183
    Certificates.certificate6126 Certificates.certificate6127

section Hyp

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {V₁ V₂ W : Subgroup G}

theorem Hyp.centralizer_radical_le
    (h : Hyp G A) (d : Datum A) (hR : Radicals d.V V₁ V₂)
    (hW : W = V₁ ∨ W = V₂) :
    ∀ x ∈ normalizer (A : Set G), (∀ w ∈ W, x * w = w * x) → x ∈ W ⊔ centralizer (A : Set G) := by
  obtain ⟨e⟩ := h.nonempty_equiv_S
  intro x hx hxw
  exact centralizer_V₁_le_of_certificate h.commutator_eq_top h.odd e d.V_isSylow hR hW
    ⟨hx, mem_centralizer_iff.2 fun w hw => (hxw w hw).symm⟩

theorem Hyp.card_fixed_le_four
    (h : Hyp G A) (d : Datum A)
    (hR : Radicals d.V V₁ V₂) (hW : W = V₁ ∨ W = V₂) :
    ∀ x ∈ normalizer (A : Set G) ⊓ normalizer (W : Set G), x ∉ W ⊔ centralizer (A : Set G) →
      Nat.card ↥(W ⊓ centralizer ({x} : Set G)) ≤ 4 := by
  obtain ⟨e⟩ := h.nonempty_equiv_S
  exact card_fixed_le_four_of_certificate h.commutator_eq_top h.odd e d.V_isSylow hR hW

theorem Hyp.relIndex_le_four
    (h : Hyp G A) (d : Datum A)
    (hR : Radicals d.V V₁ V₂) (hW : W = V₁ ∨ W = V₂) :
    ∀ E : Subgroup G, E ≤ normalizer (A : Set G) ⊓ normalizer (W : Set G) →
      (∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ centralizer (W : Set G) ∧ x * x ∈ centralizer (W : Set G)) →
      (centralizer (W : Set G)).relIndex E ≤ 4 := by
  obtain ⟨e⟩ := h.nonempty_equiv_S
  exact relIndex_le_four_of_certificate h.commutator_eq_top h.odd e d.V_isSylow hR hW

theorem Hyp.exists_regularNormal_sylow_oddComplement_of_certificate
    (h : Hyp G A) (d : Datum A) (hR : Radicals d.V V₁ V₂)
    (hW : W = V₁ ∨ W = V₂) :
    ∃ X Q O : Subgroup G, IsRegularNormal (W ⊔ zpowers d.t : Subgroup G) d.t X ∧
      IsSylowOf 2 Q X ∧ (W ⊔ zpowers d.t : Subgroup G) < Q ∧ Odd (Nat.card O) ∧
      (∀ n ∈ normalizer ((W ⊔ zpowers d.t : Subgroup G) : Set G), ∀ o ∈ O, n * o * n⁻¹ ∈ O) ∧
      O ⊔ (W ⊔ zpowers d.t : Subgroup G) = centralizer ((W ⊔ zpowers d.t : Subgroup G) : Set G) ∧
      Q ⊔ O = X ∧ Q ⊓ O = ⊥ :=
  h.exists_regularNormal_sylow_oddComplement d hR hW (h.centralizer_radical_le d hR hW)

end Hyp

end CFSG.OddStandard.Seitz77
