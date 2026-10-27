module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalSylow
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalQDerived
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalPAbelian

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem commutator_yamadaP_sup_zpowers (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    ⁅yamadaP d t ⊔ zpowers t, yamadaP d t ⊔ zpowers t⁆ = yamadaS₄ d t := by
  obtain ⟨-, -, -, -, -, hER, hker, -⟩ := h.yamada_5_32_of_layerHyp d hlay
  have hS₄c : ∀ x ∈ yamadaS₄ d t, ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaF₄ d t :=
    fun _ hx _ hy => h.commutator_mem_yamadaF₄_of_mem_yamadaS₄ d hlay hx hy
  have htS₄ : ∀ x ∈ yamadaS₄ d t, t * x * t * x⁻¹ ∈ yamadaF₄ d t :=
    fun _ hx => h.crossed_mem_yamadaF₄_of_mem_yamadaS₄ d hlay hx
  rw [hER] at hker ⊢
  exact h.commutator_yamadaR₅_sup_yamadaR₆ d hlay hker hS₄c htS₄
    (h.normalizer_yamadaR₄_le_normalizer_yamadaF₄ d hlay) (h.yamadaM₄_eq_sup d hlay)
    (h.yamadaF₃_eq_sup_map_F_QD d hlay (h.yamadaF₃_eq_sup d hlay))

theorem false_of_odd_of_layerHyp (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) (hf : Odd f) : False :=
  h.false_of_layerHyp_of_odd d hlay hf (h.commutator_yamadaP_sup_zpowers d hlay)
    (fun _ hx => h.mul_self_mem_yamadaF₄_of_mem_yamadaP d hlay hx)

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
