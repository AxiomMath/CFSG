module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalP
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalS4
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL6Three
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalR56

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem normalizer_yamadaR₄_le_normalizer_yamadaF₄ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    normalizer (yamadaR₄ d t : Set G) ≤
      normalizer (yamadaD₄ d t : Set G) ⊓ normalizer (yamadaF₄ d t : Set G) :=
  h.normalizer_yamadaD₄ d hlay (h.normalizer_yamadaR₄_le_of_layerHyp d hlay)

theorem yamada_5_32_of_layerHyp (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    normalizer (yamadaR₄ d t : Set G) = (yamadaP d t ⊔ zpowers t) ⊔
        (centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) ∧
      IsPGroup 2 (yamadaP d t) ∧ t ∉ yamadaP d t ∧ t ∈ normalizer (yamadaP d t : Set G) ∧
      d.S.map L.subtype ≤ yamadaP d t ∧
      yamadaP d t ⊔ zpowers t = yamadaR₅ d t ⊔ yamadaR₆ d t ∧
      (yamadaP d t ⊔ zpowers t) ⊓
          normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G) = yamadaR₄ d t ∧
      ∀ x ∈ yamadaP d t ⊔ zpowers t, ∀ s ∈ yamadaS₄ d t, x * s * x⁻¹ * s⁻¹ ∈ yamadaF₄ d t := by
  have hS₄c : ∀ x ∈ yamadaS₄ d t, ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaF₄ d t :=
    fun _ hx _ hy => h.commutator_mem_yamadaF₄_of_mem_yamadaS₄ d hlay hx hy
  have htS₄ : ∀ x ∈ yamadaS₄ d t, t * x * t * x⁻¹ ∈ yamadaF₄ d t :=
    fun _ hx => h.crossed_mem_yamadaF₄_of_mem_yamadaS₄ d hlay hx
  have hKDF := h.normalizer_yamadaR₄_le_normalizer_yamadaF₄ d hlay
  have hR₆N := h.yamadaR₆_le_normalizer_yamadaR₄ d hlay
  exact h.yamada_5_32 d hlay hS₄c
    (fun _ hx => h.mul_self_mem_yamadaF₄_of_mem_yamadaS₄ d hlay hx)
    (h.S_map_inf_yamadaF₄ d hlay) (h.yamadaD₄_eq_sup d hlay) (h.yamadaM₄_eq_sup d hlay)
    (hKDF.trans inf_le_right)
    (h.commutator_mem_yamadaF₄_of_mem_yamadaR₅ d hlay hS₄c htS₄)
    (h.commutator_mem_yamadaF₄_of_mem_yamadaR₆ d hlay (h.yamadaM₄_eq_sup d hlay) hS₄c htS₄
      (hR₆N.trans hKDF))
    hR₆N (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₄ d hlay)

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
