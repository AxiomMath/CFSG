module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalPTwo
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.QTwoShortcut

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open scoped commutatorElement

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem t_mem_normalizer_yamadaS₄_LS (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∈ normalizer (yamadaS₄ d t : Set G) :=
  (mem_inf.1 (mem_inf.1 (h.normalizer_yamadaR₄_le_of_layerHyp d hlay
    (le_normalizer (h.t_mem_yamadaR₄_P d hlay)))).1).1

theorem yamadaR₄_eq_sup_zpowers_LS (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaR₄ d t = yamadaS₄ d t ⊔ zpowers t := by
  have htS₄ : t ∉ yamadaS₄ d t := fun ht =>
    h.t_not_mem_centralizer_yamadaV₁ d hlay (mem_inf.1 ht).2
  have hle : yamadaS₄ d t ⊔ zpowers t ≤ yamadaR₄ d t :=
    sup_le inf_le_left (zpowers_le.2 (h.t_mem_yamadaR₄_P d hlay))
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [h.card_sup_zpowers_of_not_mem (h.t_mem_normalizer_yamadaS₄_LS d hlay) htS₄,
    h.card_yamadaR₄_S4 d hlay, h.card_yamadaS₄ d hlay]

theorem yamadaP_eq_inf_centralizer_LS (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaP d t = (yamadaP d t ⊔ zpowers t) ⊓ centralizer (yamadaV₁ d t : Set G) := by
  refine le_antisymm (le_inf le_sup_left (yamadaP_le_centralizer_yamadaV₁ d t))
    fun x hx => ?_
  obtain ⟨hxE, hxC⟩ := mem_inf.1 hx
  rcases (h.mem_sup_zpowers_iff_of_normalizer (h.t_mem_normalizer_yamadaP d hlay)).1 hxE with
    hxP | htx
  · exact hxP
  · exfalso
    apply h.t_not_mem_centralizer_yamadaV₁ d hlay
    have := mul_mem (yamadaP_le_centralizer_yamadaV₁ d t htx) (inv_mem hxC)
    rwa [mul_inv_cancel_right] at this

theorem normalizer_yamadaP_sup_zpowers (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hE' : ⁅yamadaP d t ⊔ zpowers t, yamadaP d t ⊔ zpowers t⁆ = yamadaS₄ d t)
    (hPsq : ∀ x ∈ yamadaP d t, x * x ∈ yamadaF₄ d t) :
    normalizer ((yamadaP d t ⊔ zpowers t : Subgroup G) : Set G) =
      (centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) ⊔
        yamadaP d t := by
  obtain ⟨hK, -, -, htN, -, hER, hker, -⟩ := h.yamada_5_32_of_layerHyp d hlay
  have htNCS : t ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.S.map L.subtype : Subgroup G) : Set G) :=
    mem_inf.2 ⟨mem_centralizer_singleton_iff.2 rfl, h.t_mem_normalizer_map d.S⟩
  have hP_N : yamadaP d t ≤ normalizer (yamadaR₄ d t : Set G) := by
    rw [hK]
    exact le_sup_left.trans le_sup_left
  refine le_antisymm (fun g hg => ?_) (sup_le (fun c hc => ?_) (le_sup_left.trans le_normalizer))
  ·
    have hgS₄ : g ∈ normalizer (yamadaS₄ d t : Set G) := by
      have := normalizer_le_normalizer_commutator_C8 (yamadaP d t ⊔ zpowers t) hg
      rwa [hE'] at this
    have hgN := h.normalizer_yamadaS₄_le d hlay (h.commutator_mem_yamadaY₂_of_mem_yamadaM₄ d hlay)
      (fun _ hx _ hy => h.commutator_mem_yamadaW₃_of_mem_yamadaF₄ d hlay hx hy)
      (h.yamadaS₄_eq_yamadaF₄_sup_S d hlay) hgS₄
    obtain ⟨⟨⟨hgV₁, -⟩, -⟩, -⟩ := hgN
    have hgP : g ∈ normalizer (yamadaP d t : Set G) := by
      rw [h.yamadaP_eq_inf_centralizer_LS d hlay]
      exact Common.mem_normalizer_inf hg (mem_normalizer_centralizer_C8 hgV₁)
    have hx : g * t * g⁻¹ ∈ yamadaP d t ⊔ zpowers t :=
      (mem_normalizer_iff.1 hg t).1 (mem_sup_right (mem_zpowers t))
    have htg : t * (g * t * g⁻¹) ∈ yamadaP d t := by
      rcases (h.mem_sup_zpowers_iff_of_normalizer htN).1 hx with hxP | htx
      · exfalso
        apply h.t_not_mem_yamadaP d hlay
        have := (mem_normalizer_iff.1 (inv_mem hgP) _).1 hxP
        rwa [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
      · exact htx
    set p := t * (g * t * g⁻¹) with hp
    have hxe : g * t * g⁻¹ = t * p := by
      rw [hp, ← mul_assoc, h.t_mul_t, one_mul]
    have hinv : t * p * t = p⁻¹ := by
      have h2 : (t * p) * (t * p) = 1 := by
        rw [← hxe, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, h.t_mul_t,
          mul_one, mul_inv_cancel]
      calc t * p * t = ((t * p) * (t * p)) * p⁻¹ := by group
        _ = p⁻¹ := by rw [h2, one_mul]
    have hpF₄ : p ∈ normalizer (yamadaF₄ d t : Set G) :=
      (h.normalizer_yamadaR₄_le_normalizer_yamadaF₄ d hlay (hP_N htg)).2
    have hpN : p ∈ normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G) := by
      refine h.mem_normalizer_sup_zpowers_D3 (h.t_mem_normalizer_yamadaF₄ d hlay) hpF₄ ?_
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
      have hinv' : t * p⁻¹ * t = p := by
        have := congrArg (fun x : G => x⁻¹) hinv
        simp only [mul_inv_rev, inv_inv, htinv] at this
        rw [← mul_assoc] at this
        exact this
      have e : p * t * p⁻¹ = (p * p) * t := by
        calc p * t * p⁻¹ = p * (t * p⁻¹ * t) * t⁻¹ := by group
          _ = (p * p) * t := by rw [hinv', htinv]
      rw [e]
      exact mul_mem (mem_sup_left (hPsq p htg)) (mem_sup_right (mem_zpowers t))
    have hpR₄ : p ∈ yamadaR₄ d t := by
      rw [← hker]
      exact mem_inf.2 ⟨mem_sup_left htg, hpN⟩
    have hpS₄ : p ∈ yamadaS₄ d t := mem_inf.2 ⟨hpR₄, yamadaP_le_centralizer_yamadaV₁ d t htg⟩
    have hgR₄ : g ∈ normalizer (yamadaR₄ d t : Set G) := by
      rw [h.yamadaR₄_eq_sup_zpowers_LS d hlay]
      refine h.mem_normalizer_sup_zpowers_D3 (h.t_mem_normalizer_yamadaS₄_LS d hlay) hgS₄ ?_
      rw [hxe]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hpS₄)
    rw [hK] at hgR₄
    exact (sup_le (sup_le le_sup_right ((zpowers_le.2 htNCS).trans le_sup_left)) le_sup_left)
      hgR₄
  ·
    rw [hER]
    exact Common.mem_normalizer_sup (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₅ d hc)
      (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₆ d hlay hc)

theorem commutator_mem_yamadaY₂_of_mem_yamadaP (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    ∀ y ∈ yamadaP d t, ∀ a ∈ yamadaW₃ d t, y * a * y⁻¹ * a⁻¹ ∈ yamadaY₂ d t := by
  obtain ⟨hK, -, -, -, -, -, -, -⟩ := h.yamada_5_32_of_layerHyp d hlay
  have hP_N : yamadaP d t ≤ normalizer (yamadaR₄ d t : Set G) := by
    rw [hK]
    exact le_sup_left.trans le_sup_left
  have hNY₂ : ∀ y ∈ yamadaP d t, y ∈ normalizer (yamadaY₂ d t : Set G) := fun y hy =>
    (mem_inf.1 (h.normalizer_yamadaR₄_le_of_layerHyp d hlay (hP_N hy))).2
  have hD₅W₃ : yamadaW₃ d t ≤ yamadaD₅ d t := by
    rw [(h.yamada_5_25 d (h.normalizerHyp_of_layerHyp d hlay) (h.yamada_5_6_1 d hlay)
      (h.yamada_5_6_2 d hlay) (h.yamada_5_9_1 d hlay) (h.yamada_5_9_2 d hlay)
      (h.yamada_5_9_3 d hlay) (h.yamada_5_10_1 d hlay) (h.yamada_5_10_2 d hlay)
      (h.yamadaY₂_eq d hlay) (h.yamada_5_20 d hlay) (h.yamada_5_22_1 d hlay)
      (h.yamada_5_21 d hlay)).2.2.2.1]
    exact le_sup_left
  have hle : yamadaP d t ≤ modCentralizerSub (yamadaW₃ d t) (yamadaY₂ d t) := by
    refine sup_le (fun y hy => ⟨hNY₂ y (mem_sup_left hy), fun a ha => ?_⟩)
      (fun y hy => ⟨hNY₂ y (mem_sup_right hy), fun a ha =>
        h.commutator_mem_yamadaY₂_of_mem_yamadaM₆_of_layerHyp d hlay hy ha⟩)
    have h525 := (h.yamada_5_25 d (h.normalizerHyp_of_layerHyp d hlay) (h.yamada_5_6_1 d hlay)
      (h.yamada_5_6_2 d hlay) (h.yamada_5_9_1 d hlay) (h.yamada_5_9_2 d hlay)
      (h.yamada_5_9_3 d hlay) (h.yamada_5_10_1 d hlay) (h.yamada_5_10_2 d hlay)
      (h.yamadaY₂_eq d hlay) (h.yamada_5_20 d hlay) (h.yamada_5_22_1 d hlay)
      (h.yamada_5_21 d hlay)).1
    have hc : ⁅y, a⁆ ∈ ⁅yamadaD₅ d t, yamadaD₅ d t⁆ := commutator_mem_commutator hy (hD₅W₃ ha)
    rw [h525, commutatorElement_def] at hc
    exact yamadaV₁_le_yamadaY₂ d hc
  exact fun y hy a ha => (mem_modCentralizerSub.1 (hle hy)).2 a ha

theorem false_of_layerHyp_of_odd (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) (hf : Odd f)
    (hE' : ⁅yamadaP d t ⊔ zpowers t, yamadaP d t ⊔ zpowers t⁆ = yamadaS₄ d t)
    (hPsq : ∀ x ∈ yamadaP d t, x * x ∈ yamadaF₄ d t) : False := by
  obtain ⟨-, hPp, htP, htN, hSP, -, -, -⟩ := h.yamada_5_32_of_layerHyp d hlay
  have h521 := h.yamada_5_21 d hlay
  exact h.false_of_commutator_le d hf hPp htN htP hSP
    (h.normalizer_yamadaP_sup_zpowers d hlay hE' hPsq) h521.2.1 h521.2.2
    (le_sup_right.trans (h.yamadaW₂_le_yamadaW₃ d hlay)) (h.yamada_5_9_2 d hlay).2.1
    (h.commutator_mem_yamadaY₂_of_mem_yamadaP d hlay)

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
