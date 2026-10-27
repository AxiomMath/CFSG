module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalR4
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Ten

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem yamadaR₃_le_yamadaR₄_R5 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaR₃ d t ≤ yamadaR₄ d t :=
  (h.yamadaR₃_le_sup_yamadaW₃_R4 d hlay).trans
    (sup_le (h.yamadaR₂_le_yamadaR₄_R4 d hlay) (h.yamadaW₃_le_yamadaR₄_R4 d hlay))

theorem yamadaL₃_le_yamadaR₄_R5 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaL₃ d t ≤ yamadaR₄ d t :=
  (h.yamadaL₃_le_yamadaR₃_D3 d hlay).trans (h.yamadaR₃_le_yamadaR₄_R5 d hlay)

theorem yamadaM₃_le_yamadaM₄_R5 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaM₃ d t ≤ yamadaM₄ d t :=
  le_inf ((inf_le_left : yamadaM₃ d t ≤ yamadaL₃ d t).trans
      (h.yamadaL₃_le_yamadaR₄_R5 d hlay))
    (inf_le_right : yamadaM₃ d t ≤ centralizer (yamadaY₂ d t : Set G))

theorem yamadaD₃_le_yamadaD₄_R5 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaD₃ d t ≤ yamadaD₄ d t := by
  have hD₃R₄ : yamadaD₃ d t ≤ yamadaR₄ d t :=
    ((inf_le_left : yamadaD₃ d t ≤ yamadaS₃ d t).trans
      (inf_le_left : yamadaS₃ d t ≤ yamadaR₃ d t)).trans (h.yamadaR₃_le_yamadaR₄_R5 d hlay)
  have hD₃C₅ : yamadaD₃ d t ≤ yamadaC₅ d t := inf_le_right
  have hD₃V₁ : yamadaD₃ d t ≤ centralizer (yamadaV₁ d t : Set G) :=
    (inf_le_left : yamadaD₃ d t ≤ yamadaS₃ d t).trans inf_le_right
  exact le_inf hD₃R₄ (le_inf hD₃C₅ hD₃V₁)

theorem yamadaF₃_le_yamadaF₄_R5 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaF₃ d t ≤ yamadaF₄ d t :=
  le_inf ((inf_le_left : yamadaF₃ d t ≤ yamadaM₃ d t).trans
      (h.yamadaM₃_le_yamadaM₄_R5 d hlay))
    ((inf_le_right : yamadaF₃ d t ≤ yamadaD₃ d t).trans
      (h.yamadaD₃_le_yamadaD₄_R5 d hlay))

theorem yamadaW₃_le_yamadaF₄_R5 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaW₃ d t ≤ yamadaF₄ d t :=
  (h.yamadaW₃_le_yamadaF₃ d hlay).trans (h.yamadaF₃_le_yamadaF₄_R5 d hlay)

theorem yamadaV₁_le_yamadaF₄_R5 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaV₁ d t ≤ yamadaF₄ d t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  exact (h.yamadaV₁_le_yamadaW₃_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102).trans
    (h.yamadaW₃_le_yamadaF₄_R5 d hlay)

theorem yamadaM_map_le_yamadaM₃_R5 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : d.M.map L.subtype ≤ yamadaM₃ d t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have hML₃ : d.M.map L.subtype ≤ yamadaL₃ d t :=
    (le_sup_left.trans (h.tM_le_yamadaL₂ d)).trans
      (h.yamadaL₂_le_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101 h5102)
  exact le_inf hML₃ (h.M_map_le_centralizer_yamadaY₂ d hlay)

theorem yamadaD₄_le_normalizer_yamadaF₄_R5 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaD₄ d t ≤ normalizer (yamadaF₄ d t : Set G) := by
  intro x hx
  exact Common.mem_normalizer_inf
    (h.yamadaR₄_le_normalizer_yamadaM₄_R4 d hlay ((inf_le_left : yamadaD₄ d t ≤ yamadaR₄ d t) hx))
    (le_normalizer hx)

theorem yamadaM₄_le_normalizer_yamadaF₄_R5 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaM₄ d t ≤ normalizer (yamadaF₄ d t : Set G) := by
  intro m hm
  have hmR₄ : m ∈ yamadaR₄ d t := (inf_le_left : yamadaM₄ d t ≤ yamadaR₄ d t) hm
  have hmY₂ : m ∈ centralizer (yamadaY₂ d t : Set G) :=
    (inf_le_right : yamadaM₄ d t ≤ centralizer (yamadaY₂ d t : Set G)) hm
  have hmC₅ : m ∈ normalizer (yamadaC₅ d t : Set G) :=
    (h.yamadaR₅_le_normalizer_yamadaC₅ d) ((inf_le_left : yamadaR₄ d t ≤ yamadaR₅ d t) hmR₄)
  have hmV₁ : m ∈ centralizer (yamadaV₁ d t : Set G) :=
    mem_centralizer_iff.2 fun v hv =>
      mem_centralizer_iff.1 hmY₂ v (SetLike.mem_coe.2 (yamadaV₁_le_yamadaY₂ (t := t) d hv))
  have hmD₅ : m ∈ normalizer (yamadaD₅ d t : Set G) :=
    Common.mem_normalizer_inf hmC₅
      (mem_normalizer_centralizer_C8 (Subgroup.centralizer_le_normalizer _ hmV₁))
  have hmD₄ : m ∈ normalizer (yamadaD₄ d t : Set G) :=
    Common.mem_normalizer_inf (le_normalizer hmR₄) hmD₅
  exact Common.mem_normalizer_inf (le_normalizer hm) hmD₄

theorem exists_mem_yamadaR₅_conj_eq_mod_F₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hD₄ : yamadaD₄ d t = d.D.map L.subtype ⊔ yamadaF₄ d t) {a : G} (ha : a ∈ yamadaD₄ d t) :
    ∃ x ∈ yamadaR₅ d t, ∃ b ∈ yamadaF₄ d t, x * t * x⁻¹ = t * a * b := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have hDD₄ : d.D.map L.subtype ≤ yamadaD₄ d t := by
    rw [hD₄]
    exact le_sup_left
  have hDN : d.D.map L.subtype ≤ normalizer (yamadaF₄ d t : Set G) :=
    fun δ hδ => h.yamadaD₄_le_normalizer_yamadaF₄_R5 d hlay (hDD₄ hδ)
  have ha' : a ∈ ((d.D.map L.subtype ⊔ yamadaF₄ d t : Subgroup G) : Set G) := by
    rw [← hD₄]
    exact ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hDN, Set.mem_mul] at ha'
  obtain ⟨δ, hδ, g, hg, rfl⟩ := ha'
  obtain ⟨x, hx, v, hv, hxt⟩ :=
    (h.yamada_5_12 d hNH h561 h562 h591 h592 h593).2.1.2.1 δ
      (D_le_yamadaD₁ d t (SetLike.mem_coe.1 hδ))
  refine ⟨x, (le_sup_left : yamadaC₅ d t ≤ yamadaR₅ d t) hx, g⁻¹ * v,
    mul_mem (inv_mem (SetLike.mem_coe.1 hg)) (h.yamadaV₁_le_yamadaF₄_R5 d hlay hv), ?_⟩
  rw [hxt]
  group

theorem exists_mem_yamadaR₆_conj_eq_mod_F₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hM₄ : yamadaM₄ d t = d.M.map L.subtype ⊔ yamadaF₄ d t)
    (hL₆ : ∀ m ∈ yamadaM₃ d t, ∃ x ∈ yamadaL₆ d t, ∃ w ∈ yamadaW₃ d t, x * t * x⁻¹ = t * m * w)
    {a : G} (ha : a ∈ yamadaM₄ d t) :
    ∃ x ∈ yamadaR₆ d t, ∃ b ∈ yamadaF₄ d t, x * t * x⁻¹ = t * a * b := by
  have hMM₄ : d.M.map L.subtype ≤ yamadaM₄ d t := by
    rw [hM₄]
    exact le_sup_left
  have hMN : d.M.map L.subtype ≤ normalizer (yamadaF₄ d t : Set G) :=
    fun μ hμ => h.yamadaM₄_le_normalizer_yamadaF₄_R5 d hlay (hMM₄ hμ)
  have ha' : a ∈ ((d.M.map L.subtype ⊔ yamadaF₄ d t : Subgroup G) : Set G) := by
    rw [← hM₄]
    exact ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hMN, Set.mem_mul] at ha'
  obtain ⟨μ, hμ, g, hg, rfl⟩ := ha'
  obtain ⟨x, hx, w, hw, hxt⟩ :=
    hL₆ μ (h.yamadaM_map_le_yamadaM₃_R5 d hlay (SetLike.mem_coe.1 hμ))
  refine ⟨x, yamadaL₆_le_yamadaR₆ d t hx, g⁻¹ * w,
    mul_mem (inv_mem (SetLike.mem_coe.1 hg)) (h.yamadaW₃_le_yamadaF₄_R5 d hlay hw), ?_⟩
  rw [hxt]
  group

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
