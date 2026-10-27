module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL6
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalM6
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalM6Sup
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalR4
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalR4Frattini

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem yamada_5_29_1_of_layerHyp (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaL₆ d t = yamadaM₆ d t ⊔ zpowers t ∧ t ∉ yamadaM₆ d t ∧
      yamadaM₆ d t =
        yamadaM₄ d t ⊔ (yamadaM₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom :=
  h.yamada_5_29_1 d hlay (h.yamada_5_27_1 d hlay).2.1

theorem commutator_mem_yamadaY₂_of_mem_yamadaM₆_of_layerHyp (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {m w : G}
    (hm : m ∈ yamadaM₆ d t) (hw : w ∈ yamadaW₃ d t) :
    m * w * m⁻¹ * w⁻¹ ∈ yamadaY₂ d t :=
  h.commutator_mem_yamadaY₂_of_mem_yamadaM₆ d hlay
    (le_sup_right.trans (h.yamada_5_27_1 d hlay).1.ge)
    (fun _ hx => h.conj_t_mem_of_mem_yamadaL₆ d hlay hx) (h.yamadaL₆_inf_normalizer d hlay) hm hw

theorem yamadaM₄_le_yamadaM₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaM₄ d t ≤ yamadaM₆ d t := by
  intro m hm
  obtain ⟨hmR, hmC⟩ := mem_inf.1 hm
  have hmL₄ : m ∈ yamadaL₄ d t :=
    mem_inf.2 ⟨hmR, centralizer_le (h.Y_map_le_yamadaY₂ d hlay) hmC⟩
  have hmL₆ : m ∈ yamadaL₆ d t := by
    rw [(h.yamada_5_27_1 d hlay).2.1]
    exact mem_sup_left hmL₄
  exact mem_inf.2 ⟨hmL₆, hmC⟩

theorem commutator_mem_yamadaY₂_of_mem_yamadaM₄ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    ∀ m ∈ yamadaM₄ d t, ∀ w ∈ yamadaW₃ d t, m * w * m⁻¹ * w⁻¹ ∈ yamadaY₂ d t :=
  fun _ hm _ hw => h.commutator_mem_yamadaY₂_of_mem_yamadaM₆_of_layerHyp d hlay
    (h.yamadaM₄_le_yamadaM₆ d hlay hm) hw

theorem normalizer_yamadaR₄_le_of_layerHyp (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaS₄ d t : Set G) ⊓
      normalizer (yamadaW₃ d t : Set G) ⊓ normalizer (yamadaY₂ d t : Set G) :=
  h.normalizer_yamadaR₄_le d hlay (h.commutator_mem_yamadaY₂_of_mem_yamadaM₄ d hlay)

theorem normalizer_yamadaR₄_inf_le_of_layerHyp (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    normalizer (yamadaR₄ d t : Set G) ⊓
        normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      yamadaR₄ d t ⊔ (centralizer ({t} : Set G) ⊓
        normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) :=
  h.normalizer_yamadaR₄_inf_le d hlay
    ((h.normalizer_yamadaR₄_le_of_layerHyp d hlay).trans inf_le_left)
    (fun _ ha => h.exists_mem_yamadaL₄_conj_eq d hlay ha)

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
