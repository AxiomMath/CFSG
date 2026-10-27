module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL6Two
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalR5Cover
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalR4Kernel
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalS4Centre

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open

section Defs

variable {G : Type} [Group G] {L : Subgroup G} {q : ℕ}

@[expose] noncomputable def yamadaP (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaD₅ d t ⊔ yamadaM₆ d t

theorem yamadaD₅_le_yamadaP (d : TrialityD4Data L q) (t : G) : yamadaD₅ d t ≤ yamadaP d t :=
  le_sup_left

theorem yamadaM₆_le_yamadaP (d : TrialityD4Data L q) (t : G) : yamadaM₆ d t ≤ yamadaP d t :=
  le_sup_right

theorem yamadaP_le_centralizer_yamadaV₁ (d : TrialityD4Data L q) (t : G) :
    yamadaP d t ≤ centralizer (yamadaV₁ d t : Set G) :=
  sup_le inf_le_right ((inf_le_right : yamadaM₆ d t ≤ centralizer (yamadaY₂ d t : Set G)).trans
    (centralizer_le (Setup.yamadaV₁_le_yamadaY₂ d)))

end Defs

section Generic

variable {G : Type*} [Group G]

theorem isPGroup_of_mul_self_mem_P {H Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hH : ∀ x ∈ H, x * x ∈ Q) : IsPGroup 2 H := by
  intro g
  obtain ⟨n, hn⟩ := hQ ⟨(g : G) * g, hH g g.2⟩
  refine ⟨n + 1, Subtype.ext ?_⟩
  have hn' := congrArg Subtype.val hn
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hn' ⊢
  rw [pow_succ', pow_mul, sq]
  exact hn'

end Generic

set_option hygiene false in
local macro "layer_ctx" : tactic => `(tactic| (
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h514 := h.yamada_5_14 d hNH h561 h562 h591 h592 h593))

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

theorem t_not_mem_yamadaP (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∉ yamadaP d t := fun ht =>
  h.t_not_mem_centralizer_yamadaV₁ d hlay (yamadaP_le_centralizer_yamadaV₁ d t ht)

theorem S_map_le_yamadaP (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : d.S.map L.subtype ≤ yamadaP d t := by
  have hS := h.S_map_le_yamadaS₄_R4 d hlay
  rw [h.yamadaS₄_eq_sup_yamadaD₄ d hlay] at hS
  exact hS.trans (sup_le ((h.yamadaM₄_le_yamadaM₆ d hlay).trans (yamadaM₆_le_yamadaP d t))
    ((inf_le_right : yamadaD₄ d t ≤ yamadaD₅ d t).trans (yamadaD₅_le_yamadaP d t)))

theorem t_mem_normalizer_yamadaP (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∈ normalizer (yamadaP d t : Set G) := by
  have htC₅ : t ∈ normalizer (yamadaC₅ d t : Set G) :=
    le_normalizer (yamadaC₁_le_yamadaC₅ d t (h.t_mem_yamadaC₁ d))
  have htV₁ : t ∈ normalizer (centralizer (yamadaV₁ d t : Set G) : Set G) :=
    mem_normalizer_centralizer_C8
      (normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (h.t_mem_normalizer_yamadaD₁ d))
  have htL₆ : t ∈ yamadaL₆ d t := by
    rw [(h.yamada_5_29_1_of_layerHyp d hlay).1]
    exact mem_sup_right (mem_zpowers t)
  exact Common.mem_normalizer_sup (Common.mem_normalizer_inf htC₅ htV₁)
    (Common.mem_normalizer_inf (le_normalizer htL₆)
      (mem_normalizer_centralizer_C8 (h.t_mem_normalizer_yamadaY₂ d)))

theorem yamadaP_sup_zpowers (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaP d t ⊔ zpowers t = yamadaR₅ d t ⊔ yamadaR₆ d t := by
  have hC₅ := (h.yamada_5_20 d hlay).1
  have hL₆ := (h.yamada_5_29_1_of_layerHyp d hlay).1
  have hS := h.S_map_le_yamadaP d hlay
  apply le_antisymm
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact ((inf_le_left : yamadaD₅ d t ≤ yamadaC₅ d t).trans le_sup_left).trans le_sup_left
    · exact (yamadaM₆_le_yamadaL₆ d t).trans ((yamadaL₆_le_yamadaR₆ d t).trans le_sup_right)
    · exact ((zpowers_le).2 (h.t_mem_yamadaR₅ d)).trans le_sup_left
  · refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · rw [hC₅]
      exact sup_le_sup_right (yamadaD₅_le_yamadaP d t) _
    · exact hS.trans le_sup_left
    · rw [hL₆]
      exact sup_le_sup_right (yamadaM₆_le_yamadaP d t) _
    · exact hS.trans le_sup_left

theorem yamadaR₅_le_normalizer_yamadaR₄_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaR₅ d t ≤ normalizer (yamadaR₄ d t : Set G) := by
  layer_ctx
  exact h514.2.2.2.2.2.2

theorem t_mem_yamadaR₄_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∈ yamadaR₄ d t := by
  layer_ctx
  exact h.t_mem_yamadaR₄ d hNH h561 h562 h591 h592 h593

theorem exists_mem_yamadaS₄_conj_t_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} (hx : x ∈ normalizer (yamadaR₄ d t : Set G)) :
    ∃ k ∈ yamadaS₄ d t, x * t * x⁻¹ = t * k := by
  have hxS₄ : x ∈ normalizer (yamadaS₄ d t : Set G) :=
    (mem_inf.1 (mem_inf.1 (h.normalizer_yamadaR₄_le_of_layerHyp d hlay hx)).1).1
  have hxt : x * t * x⁻¹ ∈ yamadaR₄ d t :=
    (mem_normalizer_iff.1 hx t).1 (h.t_mem_yamadaR₄_P d hlay)
  rcases h.mem_yamadaS₄_or_R4 d hlay hxt with h1 | h1
  · exfalso
    have h2 := (mem_normalizer_iff.1 (inv_mem hxS₄) _).1 h1
    rw [show x⁻¹ * (x * t * x⁻¹) * x⁻¹⁻¹ = t by group] at h2
    exact h.t_not_mem_centralizer_yamadaV₁ d hlay (mem_inf.1 h2).2
  · refine ⟨_, h1, ?_⟩
    rw [← mul_assoc, h.t_mul_t, one_mul]

theorem yamadaF₁_le_yamadaF₄_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaF₁ d t ≤ yamadaF₄ d t := by
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  rw [h.yamadaF₁_eq_sup d h561 h562]
  exact sup_le (h.F_map_le_yamadaF₄_S4C d hlay) (h.yamadaV₁_le_yamadaF₄_R5 d hlay)

theorem yamadaR₄_le_normalizer_sup_yamadaF₄_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hKF : normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaF₄ d t : Set G)) :
    yamadaR₄ d t ≤ normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G) := by
  intro r hr
  have hrF₁ : r * t * r⁻¹ ∈ yamadaF₁ d t ⊔ zpowers t :=
    (mem_normalizer_iff.1 (mem_inf.1 hr).2 t).1 (mem_sup_right (mem_zpowers t))
  exact h.mem_normalizer_sup_zpowers_D3 (h.t_mem_normalizer_yamadaF₄ d hlay)
    (hKF (le_normalizer hr)) (sup_le_sup_right (h.yamadaF₁_le_yamadaF₄_P d hlay) _ hrF₁)

theorem exists_mem_yamadaF₄_conj_t_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} (hx : x ∈ normalizer (yamadaR₄ d t : Set G))
    (hxF : x ∈ normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G)) :
    ∃ a ∈ yamadaF₄ d t, x * t * x⁻¹ = t * a := by
  obtain ⟨k, hk, hxk⟩ := h.exists_mem_yamadaS₄_conj_t_eq d hlay hx
  have hxt : x * t * x⁻¹ ∈ yamadaF₄ d t ⊔ zpowers t :=
    (mem_normalizer_iff.1 hxF t).1 (mem_sup_right (mem_zpowers t))
  rw [hxk] at hxt
  rcases (h.mem_sup_zpowers_iff_of_normalizer (h.t_mem_normalizer_yamadaF₄ d hlay)).1 hxt with
    h1 | h1
  · exfalso
    have h2 := mul_mem (yamadaF₄_le_yamadaS₄ (t := t) d h1) (inv_mem hk)
    rw [mul_inv_cancel_right] at h2
    exact h.t_not_mem_centralizer_yamadaV₁ d hlay (mem_inf.1 h2).2
  · refine ⟨k, ?_, hxk⟩
    rwa [← mul_assoc, h.t_mul_t, one_mul] at h1

@[expose] noncomputable def yamadaE₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hKF : normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaF₄ d t : Set G)) :
    Subgroup G :=
  Common.centralizerMod (normalizer (yamadaR₄ d t : Set G)) (yamadaS₄ d t) (yamadaF₄ d t)
    (fun _ hg _ hy => (mem_normalizer_iff.1 (mem_inf.1 (mem_inf.1
      (h.normalizer_yamadaR₄_le_of_layerHyp d hlay hg)).1).1 _).1 hy)
    (fun _ hg _ hb => (mem_normalizer_iff.1 (hKF hg) _).1 hb)

theorem sup_le_yamadaE₄_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    (hKF : normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaF₄ d t : Set G))
    (hR₅ : ∀ x ∈ yamadaR₅ d t, ∀ s ∈ yamadaS₄ d t, x * s * x⁻¹ * s⁻¹ ∈ yamadaF₄ d t)
    (hR₆ : ∀ x ∈ yamadaR₆ d t, ∀ s ∈ yamadaS₄ d t, x * s * x⁻¹ * s⁻¹ ∈ yamadaF₄ d t)
    (hR₆N : yamadaR₆ d t ≤ normalizer (yamadaR₄ d t : Set G)) :
    yamadaR₅ d t ⊔ yamadaR₆ d t ≤ h.yamadaE₄ d hlay hKF :=
  sup_le (fun _ hx => ⟨h.yamadaR₅_le_normalizer_yamadaR₄_P d hlay hx, hR₅ _ hx⟩)
    (fun _ hx => ⟨hR₆N hx, hR₆ _ hx⟩)

theorem mem_yamadaR₄_of_mem_yamadaE₄_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hSF : d.S.map L.subtype ⊓ yamadaF₄ d t = d.F.map L.subtype)
    (hKF : normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaF₄ d t : Set G))
    (hR₅ : ∀ x ∈ yamadaR₅ d t, ∀ s ∈ yamadaS₄ d t, x * s * x⁻¹ * s⁻¹ ∈ yamadaF₄ d t)
    (hNCS : centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaR₄ d t : Set G))
    {x : G} (hx : x ∈ h.yamadaE₄ d hlay hKF)
    (hxt : ∃ a ∈ yamadaF₄ d t, x * t * x⁻¹ = t * a) : x ∈ yamadaR₄ d t := by
  obtain ⟨a, ha, hxa⟩ := hxt
  have hxN : x ∈ normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G) :=
    h.mem_normalizer_sup_zpowers_D3 (h.t_mem_normalizer_yamadaF₄ d hlay) (hKF hx.1) (by
      rw [hxa]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left ha))
  have hmem : x ∈ ((yamadaR₄ d t ⊔ (centralizer ({t} : Set G) ⊓
      normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) : Subgroup G) : Set G) :=
    h.normalizer_yamadaR₄_inf_le_of_layerHyp d hlay (mem_inf.2 ⟨hx.1, hxN⟩)
  rw [coe_mul_of_right_le_normalizer_left _ _ hNCS, Set.mem_mul] at hmem
  obtain ⟨r, hr, c, hc, rfl⟩ := hmem
  have hrE : r ∈ h.yamadaE₄ d hlay hKF :=
    ⟨h.yamadaR₅_le_normalizer_yamadaR₄_P d hlay ((inf_le_left : yamadaR₄ d t ≤ yamadaR₅ d t) hr),
      hR₅ r ((inf_le_left : yamadaR₄ d t ≤ yamadaR₅ d t) hr)⟩
  have hcE : c ∈ h.yamadaE₄ d hlay hKF := by
    have := mul_mem (inv_mem hrE) hx
    rwa [inv_mul_cancel_left] at this
  obtain ⟨hcC, hcS⟩ := mem_inf.1 hc
  have hcF : ∀ s ∈ d.S.map L.subtype, c * s * c⁻¹ * s⁻¹ ∈ d.F.map L.subtype := by
    intro s hs
    rw [← hSF]
    exact mem_inf.2 ⟨mul_mem ((mem_normalizer_iff.1 hcS s).1 hs) (inv_mem hs),
      hcE.2 s (h.S_map_le_yamadaS₄_R4 d hlay hs)⟩
  have hcR₄ : c ∈ yamadaR₄ d t :=
    sup_le (h.S_map_le_yamadaR₄_R4 d hlay) ((zpowers_le).2 (h.t_mem_yamadaR₄_P d hlay))
      (h.mem_sup_zpowers_of_trivial_S_mod_F d hcC hcS hcF)
  exact mul_mem hr hcR₄

theorem yamadaR₅_sup_yamadaR₆_inf_normalizer_eq_P (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    (hSF : d.S.map L.subtype ⊓ yamadaF₄ d t = d.F.map L.subtype)
    (hKF : normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaF₄ d t : Set G))
    (hR₅ : ∀ x ∈ yamadaR₅ d t, ∀ s ∈ yamadaS₄ d t, x * s * x⁻¹ * s⁻¹ ∈ yamadaF₄ d t)
    (hNCS : centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaR₄ d t : Set G))
    (hEE : yamadaR₅ d t ⊔ yamadaR₆ d t ≤ h.yamadaE₄ d hlay hKF) :
    (yamadaR₅ d t ⊔ yamadaR₆ d t) ⊓
        normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G) = yamadaR₄ d t := by
  refine le_antisymm (fun x hx => ?_) (le_inf
    ((inf_le_left : yamadaR₄ d t ≤ yamadaR₅ d t).trans le_sup_left)
    (h.yamadaR₄_le_normalizer_sup_yamadaF₄_P d hlay hKF))
  obtain ⟨hxE, hxF⟩ := mem_inf.1 hx
  exact h.mem_yamadaR₄_of_mem_yamadaE₄_P d hlay hSF hKF hR₅ hNCS (hEE hxE)
    (h.exists_mem_yamadaF₄_conj_t_eq d hlay (hEE hxE).1 hxF)

theorem mul_self_mem_yamadaR₄_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hS₄sq : ∀ x ∈ yamadaS₄ d t, x * x ∈ yamadaF₄ d t)
    (hSF : d.S.map L.subtype ⊓ yamadaF₄ d t = d.F.map L.subtype)
    (hKF : normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaF₄ d t : Set G))
    (hR₅ : ∀ x ∈ yamadaR₅ d t, ∀ s ∈ yamadaS₄ d t, x * s * x⁻¹ * s⁻¹ ∈ yamadaF₄ d t)
    (hNCS : centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaR₄ d t : Set G))
    {x : G} (hx : x ∈ h.yamadaE₄ d hlay hKF) : x * x ∈ yamadaR₄ d t := by
  obtain ⟨k, hk, hxk⟩ := h.exists_mem_yamadaS₄_conj_t_eq d hlay hx.1
  have hkN : k ∈ normalizer (yamadaF₄ d t : Set G) :=
    hKF (le_normalizer ((inf_le_left : yamadaS₄ d t ≤ yamadaR₄ d t) hk))
  have hc : x * k * x⁻¹ * k⁻¹ ∈ yamadaF₄ d t := hx.2 k hk
  refine h.mem_yamadaR₄_of_mem_yamadaE₄_P d hlay hSF hKF hR₅ hNCS (mul_mem hx hx)
    ⟨k * (x * k * x⁻¹ * k⁻¹) * k⁻¹ * (k * k), mul_mem ((mem_normalizer_iff.1 hkN _).1 hc)
      (hS₄sq k hk), ?_⟩
  calc x * x * t * (x * x)⁻¹ = x * (x * t * x⁻¹) * x⁻¹ := by group
    _ = x * (t * k) * x⁻¹ := by rw [hxk]
    _ = (x * t * x⁻¹) * (x * k * x⁻¹) := by group
    _ = t * (k * (x * k * x⁻¹ * k⁻¹) * k⁻¹ * (k * k)) := by rw [hxk]; group

theorem exists_mem_sup_conj_eq_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hS₄c : ∀ x ∈ yamadaS₄ d t, ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaF₄ d t)
    (hD₄ : yamadaD₄ d t = d.D.map L.subtype ⊔ yamadaF₄ d t)
    (hM₄ : yamadaM₄ d t = d.M.map L.subtype ⊔ yamadaF₄ d t)
    (hKF : normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaF₄ d t : Set G))
    (hR₆ : ∀ x ∈ yamadaR₆ d t, ∀ s ∈ yamadaS₄ d t, x * s * x⁻¹ * s⁻¹ ∈ yamadaF₄ d t)
    {s : G} (hs : s ∈ yamadaS₄ d t) :
    ∃ e ∈ yamadaR₅ d t ⊔ yamadaR₆ d t, ∃ b ∈ yamadaF₄ d t, e * t * e⁻¹ = t * s * b := by
  have hD₄S₄ : yamadaD₄ d t ≤ yamadaS₄ d t :=
    inf_le_inf_left _ (inf_le_right : yamadaD₅ d t ≤ centralizer (yamadaV₁ d t : Set G))
  have hF₄S₄ : yamadaF₄ d t ≤ yamadaS₄ d t := yamadaF₄_le_yamadaS₄ d
  have hS₄N : yamadaS₄ d t ≤ normalizer (yamadaF₄ d t : Set G) := fun u hu =>
    hKF (le_normalizer ((inf_le_left : yamadaS₄ d t ≤ yamadaR₄ d t) hu))
  have hMD : yamadaM₄ d t ≤ normalizer (yamadaD₄ d t : Set G) := by
    intro m hm
    refine mem_normalizer_fintype fun a ha => ?_
    have h1 := hS₄c m (yamadaM₄_le_yamadaS₄_R4 d t hm) a (hD₄S₄ ha)
    have h2 := mul_mem (yamadaF₄_le_yamadaD₄ d t h1) ha
    rwa [show m * a * m⁻¹ * a⁻¹ * a = m * a * m⁻¹ by group] at h2
  have hs' : s ∈ ((yamadaM₄ d t ⊔ yamadaD₄ d t : Subgroup G) : Set G) := by
    rw [← h.yamadaS₄_eq_sup_yamadaD₄ d hlay]
    exact hs
  rw [coe_mul_of_left_le_normalizer_right _ _ hMD, Set.mem_mul] at hs'
  obtain ⟨m, hm, a, ha, rfl⟩ := hs'
  obtain ⟨x, hx, b₁, hb₁, hxt⟩ := h.exists_mem_yamadaR₆_conj_eq_mod_F₄ d hlay hM₄
    (fun _ hm => h.exists_mem_yamadaL₆_conj_eq d hlay hm) (SetLike.mem_coe.1 hm)
  obtain ⟨y, hy, b₂, hb₂, hyt⟩ :=
    h.exists_mem_yamadaR₅_conj_eq_mod_F₄ d hlay hD₄ (SetLike.mem_coe.1 ha)
  have haS₄ : a ∈ yamadaS₄ d t := hD₄S₄ (SetLike.mem_coe.1 ha)
  have hc := hR₆ x hx (a * b₂) (mul_mem haS₄ (hF₄S₄ hb₂))
  have hF : a⁻¹ * (b₁ * (x * (a * b₂) * x⁻¹ * (a * b₂)⁻¹)) * a ∈ yamadaF₄ d t := by
    have := (mem_normalizer_iff.1 (inv_mem (hS₄N haS₄)) _).1 (mul_mem hb₁ hc)
    rwa [inv_inv] at this
  refine ⟨x * y, mul_mem (mem_sup_right hx) (mem_sup_left hy),
    a⁻¹ * (b₁ * (x * (a * b₂) * x⁻¹ * (a * b₂)⁻¹)) * a * b₂, mul_mem hF hb₂, ?_⟩
  calc x * y * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ := by group
    _ = x * (t * a * b₂) * x⁻¹ := by rw [hyt]
    _ = (x * t * x⁻¹) * (x * (a * b₂) * x⁻¹) := by group
    _ = (t * m * b₁) * (x * (a * b₂) * x⁻¹ * (a * b₂)⁻¹ * (a * b₂)) := by rw [hxt]; group
    _ = t * (m * a) * (a⁻¹ * (b₁ * (x * (a * b₂) * x⁻¹ * (a * b₂)⁻¹)) * a * b₂) := by group

theorem normalizer_yamadaR₄_le_sup_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hKF : normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaF₄ d t : Set G))
    (hNCS : centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaR₄ d t : Set G))
    (hEK : yamadaR₅ d t ⊔ yamadaR₆ d t ≤ normalizer (yamadaR₄ d t : Set G))
    (hcov : ∀ s ∈ yamadaS₄ d t, ∃ e ∈ yamadaR₅ d t ⊔ yamadaR₆ d t, ∃ b ∈ yamadaF₄ d t,
      e * t * e⁻¹ = t * s * b) :
    normalizer (yamadaR₄ d t : Set G) ≤ (yamadaR₅ d t ⊔ yamadaR₆ d t) ⊔
      (centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) := by
  intro g hg
  obtain ⟨k, hk, hgk⟩ := h.exists_mem_yamadaS₄_conj_t_eq d hlay hg
  obtain ⟨e, he, b, hb, het⟩ := hcov k hk
  have hy : e⁻¹ * g ∈ normalizer (yamadaR₄ d t : Set G) := mul_mem (inv_mem (hEK he)) hg
  have hyt : e⁻¹ * g * t * (e⁻¹ * g)⁻¹ = t * (e⁻¹ * b⁻¹ * e) := by
    have h1 : t * k = e * t * e⁻¹ * b⁻¹ := by rw [het]; group
    calc e⁻¹ * g * t * (e⁻¹ * g)⁻¹ = e⁻¹ * (g * t * g⁻¹) * e := by group
      _ = e⁻¹ * (t * k) * e := by rw [hgk]
      _ = e⁻¹ * (e * t * e⁻¹ * b⁻¹) * e := by rw [h1]
      _ = t * (e⁻¹ * b⁻¹ * e) := by group
  have hF : e⁻¹ * b⁻¹ * e ∈ yamadaF₄ d t := by
    have := (mem_normalizer_iff.1 (inv_mem (hKF (hEK he))) _).1 (inv_mem hb)
    rwa [inv_inv] at this
  have hyN : e⁻¹ * g ∈ normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G) :=
    h.mem_normalizer_sup_zpowers_D3 (h.t_mem_normalizer_yamadaF₄ d hlay) (hKF hy) (by
      rw [hyt]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hF))
  have hmem : e⁻¹ * g ∈ ((yamadaR₄ d t ⊔ (centralizer ({t} : Set G) ⊓
      normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) : Subgroup G) : Set G) :=
    h.normalizer_yamadaR₄_inf_le_of_layerHyp d hlay (mem_inf.2 ⟨hy, hyN⟩)
  rw [coe_mul_of_right_le_normalizer_left _ _ hNCS, Set.mem_mul] at hmem
  obtain ⟨r, hr, c, hc, hrc⟩ := hmem
  have hg_eq : g = e * r * c := by
    rw [mul_assoc, hrc]
    group
  rw [hg_eq]
  exact mul_mem (mem_sup_left (mul_mem he (((inf_le_left : yamadaR₄ d t ≤ yamadaR₅ d t).trans
    le_sup_left) (SetLike.mem_coe.1 hr)))) (mem_sup_right hc)

theorem normalizer_yamadaR₄_eq_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hKF : normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaF₄ d t : Set G))
    (hNCS : centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaR₄ d t : Set G))
    (hEK : yamadaR₅ d t ⊔ yamadaR₆ d t ≤ normalizer (yamadaR₄ d t : Set G))
    (hcov : ∀ s ∈ yamadaS₄ d t, ∃ e ∈ yamadaR₅ d t ⊔ yamadaR₆ d t, ∃ b ∈ yamadaF₄ d t,
      e * t * e⁻¹ = t * s * b) :
    normalizer (yamadaR₄ d t : Set G) = (yamadaP d t ⊔ zpowers t) ⊔
      (centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) := by
  rw [h.yamadaP_sup_zpowers d hlay]
  exact le_antisymm (h.normalizer_yamadaR₄_le_sup_P d hlay hKF hNCS hEK hcov) (sup_le hEK hNCS)

theorem isPGroup_yamadaP (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hS₄sq : ∀ x ∈ yamadaS₄ d t, x * x ∈ yamadaF₄ d t)
    (hSF : d.S.map L.subtype ⊓ yamadaF₄ d t = d.F.map L.subtype)
    (hKF : normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaF₄ d t : Set G))
    (hR₅ : ∀ x ∈ yamadaR₅ d t, ∀ s ∈ yamadaS₄ d t, x * s * x⁻¹ * s⁻¹ ∈ yamadaF₄ d t)
    (hNCS : centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaR₄ d t : Set G))
    (hEE : yamadaR₅ d t ⊔ yamadaR₆ d t ≤ h.yamadaE₄ d hlay hKF) :
    IsPGroup 2 (yamadaP d t) :=
  isPGroup_of_mul_self_mem_P ((h.isPGroup_yamadaR₅ d).to_le
      (inf_le_left : yamadaR₄ d t ≤ yamadaR₅ d t)) fun _ hx =>
    h.mul_self_mem_yamadaR₄_P d hlay hS₄sq hSF hKF hR₅ hNCS
      (hEE ((le_sup_left : yamadaP d t ≤ yamadaP d t ⊔ zpowers t).trans
        (h.yamadaP_sup_zpowers d hlay).le hx))

theorem yamada_5_32 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    (hS₄c : ∀ x ∈ yamadaS₄ d t, ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaF₄ d t)
    (hS₄sq : ∀ x ∈ yamadaS₄ d t, x * x ∈ yamadaF₄ d t)
    (hSF : d.S.map L.subtype ⊓ yamadaF₄ d t = d.F.map L.subtype)
    (hD₄ : yamadaD₄ d t = d.D.map L.subtype ⊔ yamadaF₄ d t)
    (hM₄ : yamadaM₄ d t = d.M.map L.subtype ⊔ yamadaF₄ d t)
    (hKF : normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaF₄ d t : Set G))
    (hR₅ : ∀ x ∈ yamadaR₅ d t, ∀ s ∈ yamadaS₄ d t, x * s * x⁻¹ * s⁻¹ ∈ yamadaF₄ d t)
    (hR₆ : ∀ x ∈ yamadaR₆ d t, ∀ s ∈ yamadaS₄ d t, x * s * x⁻¹ * s⁻¹ ∈ yamadaF₄ d t)
    (hR₆N : yamadaR₆ d t ≤ normalizer (yamadaR₄ d t : Set G))
    (hNCS : centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaR₄ d t : Set G)) :
    normalizer (yamadaR₄ d t : Set G) = (yamadaP d t ⊔ zpowers t) ⊔
        (centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) ∧
      IsPGroup 2 (yamadaP d t) ∧ t ∉ yamadaP d t ∧ t ∈ normalizer (yamadaP d t : Set G) ∧
      d.S.map L.subtype ≤ yamadaP d t ∧
      yamadaP d t ⊔ zpowers t = yamadaR₅ d t ⊔ yamadaR₆ d t ∧
      (yamadaP d t ⊔ zpowers t) ⊓
          normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G) = yamadaR₄ d t ∧
      ∀ x ∈ yamadaP d t ⊔ zpowers t, ∀ s ∈ yamadaS₄ d t, x * s * x⁻¹ * s⁻¹ ∈ yamadaF₄ d t := by
  have hEE := h.sup_le_yamadaE₄_P d hlay hKF hR₅ hR₆ hR₆N
  have hPE := h.yamadaP_sup_zpowers d hlay
  refine ⟨h.normalizer_yamadaR₄_eq_P d hlay hKF hNCS (fun x hx => (hEE hx).1) fun s hs =>
      h.exists_mem_sup_conj_eq_P d hlay hS₄c hD₄ hM₄ hKF hR₆ hs,
    h.isPGroup_yamadaP d hlay hS₄sq hSF hKF hR₅ hNCS hEE, h.t_not_mem_yamadaP d hlay,
    h.t_mem_normalizer_yamadaP d hlay, h.S_map_le_yamadaP d hlay, hPE, ?_, fun x hx => ?_⟩
  · rw [hPE]
    exact h.yamadaR₅_sup_yamadaR₆_inf_normalizer_eq_P d hlay hSF hKF hR₅ hNCS hEE
  · rw [hPE] at hx
    exact (hEE hx).2

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
