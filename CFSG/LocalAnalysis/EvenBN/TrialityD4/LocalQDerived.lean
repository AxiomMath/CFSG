module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL6Three
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalR56
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalS4Centre

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open scoped commutatorElement Pointwise

section Generic

variable {G : Type*} [Group G] {t : G}

theorem conj_inv_t_eq_QD {y m : G} (hym : y * t * y⁻¹ = t * m) :
    y⁻¹ * t * y = t * (y⁻¹ * m⁻¹ * y) := by
  have h1 : y⁻¹ * t * y * (y⁻¹ * m * y) = t := by
    calc y⁻¹ * t * y * (y⁻¹ * m * y) = y⁻¹ * (t * m) * y := by group
      _ = y⁻¹ * (y * t * y⁻¹) * y := by rw [hym]
      _ = t := by group
  rw [eq_mul_inv_of_mul_eq h1]
  group

theorem conj_quotient_t_eq_QD {g g' a a' : G} (hg : g * t * g⁻¹ = t * a)
    (hg' : g' * t * g'⁻¹ = t * a') :
    g'⁻¹ * g * t * (g'⁻¹ * g)⁻¹ = t * (g'⁻¹ * (a'⁻¹ * a) * g') := by
  calc g'⁻¹ * g * t * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * t * g⁻¹) * g' := by group
    _ = g'⁻¹ * (t * a) * g' := by rw [hg]
    _ = (g'⁻¹ * t * g') * (g'⁻¹ * a * g') := by group
    _ = (t * (g'⁻¹ * a'⁻¹ * g')) * (g'⁻¹ * a * g') := by rw [conj_inv_t_eq_QD hg']
    _ = t * (g'⁻¹ * (a'⁻¹ * a) * g') := by group

theorem conj_mul_t_eq_QD {x y a b : G} (hx : x * t * x⁻¹ = t * a) (hy : y * t * y⁻¹ = t * b) :
    x * y * t * (x * y)⁻¹ = t * (a * (x * b * x⁻¹)) := by
  calc x * y * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ := by group
    _ = x * (t * b) * x⁻¹ := by rw [hy]
    _ = (x * t * x⁻¹) * (x * b * x⁻¹) := by group
    _ = t * a * (x * b * x⁻¹) := by rw [hx]
    _ = t * (a * (x * b * x⁻¹)) := by group

theorem inv_conj_mem_QD {N : Subgroup G} {g a : G} (hg : g ∈ normalizer (N : Set G))
    (ha : a ∈ N) : g⁻¹ * a * g ∈ N := by
  have := (mem_normalizer_iff.1 (inv_mem hg) a).1 ha
  rwa [inv_inv] at this

theorem conj_commutator_t_eq_QD {y s m : G} (hym : y * t * y⁻¹ = t * m) (hst : s * t = t * s) :
    y * s * y⁻¹ * s⁻¹ * t * (y * s * y⁻¹ * s⁻¹)⁻¹ =
      t * (y * ((y⁻¹ * m * y) * s * (y⁻¹ * m * y)⁻¹ * s⁻¹) * y⁻¹) := by
  have hst' : s⁻¹ * t * s = t := by rw [mul_assoc, ← hst, inv_mul_cancel_left]
  calc y * s * y⁻¹ * s⁻¹ * t * (y * s * y⁻¹ * s⁻¹)⁻¹
      = y * s * y⁻¹ * (s⁻¹ * t * s) * y * s⁻¹ * y⁻¹ := by group
    _ = y * s * (y⁻¹ * t * y) * s⁻¹ * y⁻¹ := by rw [hst']; group
    _ = y * s * (t * (y⁻¹ * m⁻¹ * y)) * s⁻¹ * y⁻¹ := by rw [conj_inv_t_eq_QD hym]
    _ = y * (s * t) * (y⁻¹ * m⁻¹ * y) * s⁻¹ * y⁻¹ := by group
    _ = y * (t * s) * (y⁻¹ * m⁻¹ * y) * s⁻¹ * y⁻¹ := by rw [hst]
    _ = (y * t * y⁻¹) * (y * s * y⁻¹ * m⁻¹ * y * s⁻¹ * y⁻¹) := by group
    _ = t * m * (y * s * y⁻¹ * m⁻¹ * y * s⁻¹ * y⁻¹) := by rw [hym]
    _ = t * (y * ((y⁻¹ * m * y) * s * (y⁻¹ * m * y)⁻¹ * s⁻¹) * y⁻¹) := by group

theorem exists_conj_commutator_QD {N : Subgroup G} {x s y x₃ w₀ n : G}
    (hxN : x ∈ normalizer (N : Set G)) (hsN : s ∈ normalizer (N : Set G))
    (hyN : y ∈ normalizer (N : Set G)) (hx₃N : x₃ ∈ normalizer (N : Set G))
    (hw₀ : w₀ ∈ N) (hn : n ∈ N) (hc : x * s * x⁻¹ * s⁻¹ = x₃ * n)
    (hw₁ : y⁻¹ * (x * w₀) * y * (x * w₀)⁻¹ ∈ N) (hw₅ : y * x₃ * y⁻¹ * x₃⁻¹ ∈ N) :
    ∃ w ∈ N, y * ((y⁻¹ * (x * w₀) * y) * s * (y⁻¹ * (x * w₀) * y)⁻¹ * s⁻¹) * y⁻¹ = x₃ * w := by
  have hws : w₀ * s * w₀⁻¹ * s⁻¹ ∈ N := by
    have := mul_mem hw₀ ((mem_normalizer_iff.1 hsN w₀⁻¹).1 (inv_mem hw₀))
    rwa [← mul_assoc, ← mul_assoc] at this
  obtain ⟨w₁, hw₁def⟩ : ∃ w₁, w₁ = y⁻¹ * (x * w₀) * y * (x * w₀)⁻¹ := ⟨_, rfl⟩
  rw [← hw₁def] at hw₁
  have hm' : y⁻¹ * (x * w₀) * y = w₁ * x * w₀ := by rw [hw₁def]; group
  have hA : w₁ * (x * (w₀ * s * w₀⁻¹ * s⁻¹) * x⁻¹) ∈ N :=
    mul_mem hw₁ ((mem_normalizer_iff.1 hxN _).1 hws)
  have hB : s * w₁⁻¹ * s⁻¹ ∈ N := (mem_normalizer_iff.1 hsN _).1 (inv_mem hw₁)
  have hw₆ : (x₃⁻¹ * (w₁ * (x * (w₀ * s * w₀⁻¹ * s⁻¹) * x⁻¹)) * x₃) * n *
      (s * w₁⁻¹ * s⁻¹) ∈ N :=
    mul_mem (mul_mem (inv_conj_mem_QD hx₃N hA) hn) hB
  refine ⟨(x₃⁻¹ * (y * x₃ * y⁻¹ * x₃⁻¹) * x₃) *
    (y * ((x₃⁻¹ * (w₁ * (x * (w₀ * s * w₀⁻¹ * s⁻¹) * x⁻¹)) * x₃) * n * (s * w₁⁻¹ * s⁻¹)) *
      y⁻¹), mul_mem (inv_conj_mem_QD hx₃N hw₅) ((mem_normalizer_iff.1 hyN _).1 hw₆), ?_⟩
  have e1 : y * ((y⁻¹ * (x * w₀) * y) * s * (y⁻¹ * (x * w₀) * y)⁻¹ * s⁻¹) * y⁻¹ =
      y * ((w₁ * (x * (w₀ * s * w₀⁻¹ * s⁻¹) * x⁻¹)) * (x * s * x⁻¹ * s⁻¹) *
        (s * w₁⁻¹ * s⁻¹)) * y⁻¹ := by
    rw [hm']
    group
  rw [e1, hc]
  group

end Generic

set_option hygiene false in
local macro "layer_ctx" : tactic => `(tactic| (
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have h59e := h.yamadaY₂_eq d hlay
  have h520 := h.yamada_5_20 d hlay
  have h521 := h.yamada_5_21 d hlay
  have h5221 := h.yamada_5_22_1 d hlay
  have h514 := h.yamada_5_14 d hNH h561 h562 h591 h592 h593
  have h524 := h.yamada_5_24 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221
  have h525 := h.yamada_5_25 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521))

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

section Abelian

theorem t_mem_yamadaR₄_QD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∈ yamadaR₄ d t := by
  layer_ctx
  exact h.t_mem_yamadaR₄ d hNH h561 h562 h591 h592 h593

theorem sup_le_normalizer_yamadaR₄_QD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaR₅ d t ⊔ yamadaR₆ d t ≤ normalizer (yamadaR₄ d t : Set G) := by
  layer_ctx
  exact sup_le h514.2.2.2.2.2.2 (h.yamadaR₆_le_normalizer_yamadaR₄ d hlay)

theorem exists_mem_yamadaS₄_conj_t_eq_QD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} (hx : x ∈ normalizer (yamadaR₄ d t : Set G)) :
    ∃ k ∈ yamadaS₄ d t, x * t * x⁻¹ = t * k := by
  have hxS₄ : x ∈ normalizer (yamadaS₄ d t : Set G) :=
    (mem_inf.1 (mem_inf.1 (h.normalizer_yamadaR₄_le_of_layerHyp d hlay hx)).1).1
  have hxt : x * t * x⁻¹ ∈ yamadaR₄ d t :=
    (mem_normalizer_iff.1 hx t).1 (h.t_mem_yamadaR₄_QD d hlay)
  rcases h.mem_yamadaS₄_or_R4 d hlay hxt with h1 | h1
  · exfalso
    have h2 := (mem_normalizer_iff.1 (inv_mem hxS₄) _).1 h1
    rw [show x⁻¹ * (x * t * x⁻¹) * x⁻¹⁻¹ = t by group] at h2
    exact h.t_not_mem_centralizer_yamadaV₁ d hlay (mem_inf.1 h2).2
  · refine ⟨_, h1, ?_⟩
    rw [← mul_assoc, h.t_mul_t, one_mul]

theorem sup_le_modCentralizerSub_QD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hS₄c : ∀ x ∈ yamadaS₄ d t, ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaF₄ d t)
    (htS₄ : ∀ x ∈ yamadaS₄ d t, t * x * t * x⁻¹ ∈ yamadaF₄ d t)
    (hKF : normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaD₄ d t : Set G) ⊓
      normalizer (yamadaF₄ d t : Set G))
    (hM₄ : yamadaM₄ d t = d.M.map L.subtype ⊔ yamadaF₄ d t) :
    yamadaR₅ d t ⊔ yamadaR₆ d t ≤ modCentralizerSub (yamadaS₄ d t) (yamadaF₄ d t) := by
  have hEK := h.sup_le_normalizer_yamadaR₄_QD d hlay
  have hR₅ := h.commutator_mem_yamadaF₄_of_mem_yamadaR₅ d hlay hS₄c htS₄
  have hR₆ := h.commutator_mem_yamadaF₄_of_mem_yamadaR₆ d hlay hM₄ hS₄c htS₄ fun x hx =>
    hKF (h.yamadaR₆_le_normalizer_yamadaR₄ d hlay hx)
  exact sup_le (fun x hx => mem_modCentralizerSub.2 ⟨(hKF (hEK (mem_sup_left hx))).2, hR₅ x hx⟩)
    (fun x hx => mem_modCentralizerSub.2 ⟨(hKF (hEK (mem_sup_right hx))).2, hR₆ x hx⟩)

theorem inv_mul_mul_mem_normalizer_QD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hS₄c : ∀ x ∈ yamadaS₄ d t, ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaF₄ d t)
    (hKF : normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaF₄ d t : Set G))
    (hEC : yamadaR₅ d t ⊔ yamadaR₆ d t ≤ modCentralizerSub (yamadaS₄ d t) (yamadaF₄ d t))
    {x y : G} (hx : x ∈ yamadaR₅ d t ⊔ yamadaR₆ d t) (hy : y ∈ yamadaR₅ d t ⊔ yamadaR₆ d t) :
    (y * x)⁻¹ * (x * y) ∈ normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G) := by
  have hEK := h.sup_le_normalizer_yamadaR₄_QD d hlay
  obtain ⟨kx, hkx, hxt⟩ := h.exists_mem_yamadaS₄_conj_t_eq_QD d hlay (hEK hx)
  obtain ⟨ky, hky, hyt⟩ := h.exists_mem_yamadaS₄_conj_t_eq_QD d hlay (hEK hy)
  have hS₄N : ∀ k ∈ yamadaS₄ d t, k ∈ normalizer (yamadaF₄ d t : Set G) := fun k hk =>
    hKF (le_normalizer ((inf_le_left : yamadaS₄ d t ≤ yamadaR₄ d t) hk))
  have hfx := (mem_modCentralizerSub.1 (hEC hx)).2 ky hky
  have hfy := (mem_modCentralizerSub.1 (hEC hy)).2 kx hkx
  have hF : (ky * (y * kx * y⁻¹))⁻¹ * (kx * (x * ky * x⁻¹)) ∈ yamadaF₄ d t := by
    have e : (ky * (y * kx * y⁻¹))⁻¹ * (kx * (x * ky * x⁻¹)) =
        (kx⁻¹ * (y * kx * y⁻¹ * kx⁻¹)⁻¹ * kx) * (kx⁻¹ * ky⁻¹ * kx⁻¹⁻¹ * ky⁻¹⁻¹) *
          (ky⁻¹ * (x * ky * x⁻¹ * ky⁻¹) * ky) := by group
    rw [e]
    exact mul_mem (mul_mem (inv_conj_mem_QD (hS₄N kx hkx) (inv_mem hfy))
      (hS₄c _ (inv_mem hkx) _ (inv_mem hky))) (inv_conj_mem_QD (hS₄N ky hky) hfx)
  have hq := conj_quotient_t_eq_QD (conj_mul_t_eq_QD hxt hyt) (conj_mul_t_eq_QD hyt hxt)
  have hyxN : y * x ∈ normalizer (yamadaF₄ d t : Set G) := hKF (hEK (mul_mem hy hx))
  have hxyN : x * y ∈ normalizer (yamadaF₄ d t : Set G) := hKF (hEK (mul_mem hx hy))
  refine h.mem_normalizer_sup_zpowers_D3 (h.t_mem_normalizer_yamadaF₄ d hlay)
    (mul_mem (inv_mem hyxN) hxyN) ?_
  rw [hq]
  exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (inv_conj_mem_QD hyxN hF))

theorem commutator_sup_le_yamadaR₄_QD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hker : (yamadaR₅ d t ⊔ yamadaR₆ d t) ⊓
      normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G) = yamadaR₄ d t)
    (hS₄c : ∀ x ∈ yamadaS₄ d t, ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaF₄ d t)
    (hKF : normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaF₄ d t : Set G))
    (hEC : yamadaR₅ d t ⊔ yamadaR₆ d t ≤ modCentralizerSub (yamadaS₄ d t) (yamadaF₄ d t)) :
    ⁅yamadaR₅ d t ⊔ yamadaR₆ d t, yamadaR₅ d t ⊔ yamadaR₆ d t⁆ ≤ yamadaR₄ d t := by
  rw [commutator_le]
  intro x hx y hy
  have hmem : ⁅x, y⁆ ∈ (yamadaR₅ d t ⊔ yamadaR₆ d t) ⊓
      normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G) := by
    refine mem_inf.2 ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
    · have := h.inv_mul_mul_mem_normalizer_QD d hlay hS₄c hKF hEC (inv_mem hx) (inv_mem hy)
      rwa [show (y⁻¹ * x⁻¹)⁻¹ * (x⁻¹ * y⁻¹) = ⁅x, y⁆ by
        rw [commutatorElement_def]; group] at this
  rwa [hker] at hmem

theorem S_map_le_yamadaD₅_sup_QD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : d.S.map L.subtype ≤ yamadaD₅ d t ⊔ yamadaM₆ d t := by
  have hS := h.S_map_le_yamadaS₄_R4 d hlay
  rw [h.yamadaS₄_eq_sup_yamadaD₄ d hlay] at hS
  exact hS.trans (sup_le ((h.yamadaM₄_le_yamadaM₆ d hlay).trans le_sup_right)
    ((inf_le_right : yamadaD₄ d t ≤ yamadaD₅ d t).trans le_sup_left))

theorem t_mem_normalizer_yamadaD₅_sup_QD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    t ∈ normalizer ((yamadaD₅ d t ⊔ yamadaM₆ d t : Subgroup G) : Set G) := by
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

theorem yamadaD₅_sup_zpowers_QD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    (yamadaD₅ d t ⊔ yamadaM₆ d t) ⊔ zpowers t = yamadaR₅ d t ⊔ yamadaR₆ d t := by
  have hC₅ := (h.yamada_5_20 d hlay).1
  have hL₆ := (h.yamada_5_29_1_of_layerHyp d hlay).1
  have hS := h.S_map_le_yamadaD₅_sup_QD d hlay
  apply le_antisymm
  · refine sup_le (sup_le ?_ ?_) ?_
    · exact ((inf_le_left : yamadaD₅ d t ≤ yamadaC₅ d t).trans le_sup_left).trans le_sup_left
    · exact (yamadaM₆_le_yamadaL₆ d t).trans ((yamadaL₆_le_yamadaR₆ d t).trans le_sup_right)
    · exact ((zpowers_le).2 (h.t_mem_yamadaR₅ d)).trans le_sup_left
  · refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · rw [hC₅]
      exact sup_le_sup_right le_sup_left _
    · exact hS.trans le_sup_left
    · rw [hL₆]
      exact sup_le_sup_right le_sup_right _
    · exact hS.trans le_sup_left

theorem commutator_sup_le_yamadaD₅_sup_QD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    ⁅yamadaR₅ d t ⊔ yamadaR₆ d t, yamadaR₅ d t ⊔ yamadaR₆ d t⁆ ≤
      yamadaD₅ d t ⊔ yamadaM₆ d t := by
  rw [← h.yamadaD₅_sup_zpowers_QD d hlay]
  refine commutator_sup_le_C8 ((zpowers_le).2 (h.t_mem_normalizer_yamadaD₅_sup_QD d hlay)) ?_
  rw [commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hg₁
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg₂
  rw [commutatorElement_eq_one_iff_mul_comm.2 (Commute.zpow_zpow_self t m n).eq]
  exact one_mem _

theorem commutator_sup_le_yamadaS₄_QD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hker : (yamadaR₅ d t ⊔ yamadaR₆ d t) ⊓
      normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G) = yamadaR₄ d t)
    (hS₄c : ∀ x ∈ yamadaS₄ d t, ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaF₄ d t)
    (hKF : normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaF₄ d t : Set G))
    (hEC : yamadaR₅ d t ⊔ yamadaR₆ d t ≤ modCentralizerSub (yamadaS₄ d t) (yamadaF₄ d t)) :
    ⁅yamadaR₅ d t ⊔ yamadaR₆ d t, yamadaR₅ d t ⊔ yamadaR₆ d t⁆ ≤ yamadaS₄ d t :=
  le_inf (h.commutator_sup_le_yamadaR₄_QD d hlay hker hS₄c hKF hEC)
    ((h.commutator_sup_le_yamadaD₅_sup_QD d hlay).trans (sup_le inf_le_right
      ((inf_le_right : yamadaM₆ d t ≤ centralizer (yamadaY₂ d t : Set G)).trans
        (centralizer_le (yamadaV₁_le_yamadaY₂ d)))))

end Abelian

section Commutator

theorem yamadaD₁_le_commutator_QD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaD₁ d t ≤ ⁅yamadaR₅ d t ⊔ yamadaR₆ d t, yamadaR₅ d t ⊔ yamadaR₆ d t⁆ := by
  layer_ctx
  rw [← h525.2.1]
  exact commutator_mono ((le_sup_left : yamadaC₅ d t ≤ yamadaR₅ d t).trans le_sup_left)
    ((le_sup_left : yamadaC₅ d t ≤ yamadaR₅ d t).trans le_sup_left)

theorem yamadaF₃_le_commutator_QD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaF₃ d t ≤ ⁅yamadaR₅ d t ⊔ yamadaR₆ d t, yamadaR₅ d t ⊔ yamadaR₆ d t⁆ := by
  layer_ctx
  rw [← h524.2.2]
  exact commutator_mono ((inf_le_left : yamadaR₄ d t ≤ yamadaR₅ d t).trans le_sup_left)
    ((inf_le_left : yamadaR₄ d t ≤ yamadaR₅ d t).trans le_sup_left)

theorem yamadaM₃_le_commutator_QD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaM₃ d t ≤ ⁅yamadaR₅ d t ⊔ yamadaR₆ d t, yamadaR₅ d t ⊔ yamadaR₆ d t⁆ := by
  have hF₃ := h.yamadaF₃_le_commutator_QD d hlay
  have htE : t ∈ yamadaR₅ d t ⊔ yamadaR₆ d t := mem_sup_left (h.t_mem_yamadaR₅ d)
  have htN : t ∈ normalizer
      ((⁅yamadaR₅ d t ⊔ yamadaR₆ d t, yamadaR₅ d t ⊔ yamadaR₆ d t⁆ : Subgroup G) : Set G) :=
    normalizer_le_normalizer_commutator_C8 _ (le_normalizer htE)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  rw [h.yamadaM₃_eq_sup d hlay]
  refine sup_le hF₃ fun b hb => ?_
  obtain ⟨x, hx, w, hw, hxt⟩ := h.exists_mem_map_conj_yamadaL₄_conj_eq d hlay hb
  have hxE : x ∈ yamadaR₅ d t ⊔ yamadaR₆ d t :=
    mem_sup_right (yamadaL₆_le_yamadaR₆ d t (h.yamadaT₆_le_yamadaL₆ d hlay
      (h.map_conj_yamadaL₄_le_yamadaT₆ d hlay hx)))
  have h1 : x * t * x⁻¹ * t⁻¹ ∈
      ⁅yamadaR₅ d t ⊔ yamadaR₆ d t, yamadaR₅ d t ⊔ yamadaR₆ d t⁆ := by
    have := commutator_mem_commutator hxE htE
    rwa [commutatorElement_def] at this
  rw [hxt, htinv] at h1
  have h2 := (mem_normalizer_iff.1 htN _).1 h1
  have h3 : b * w ∈ ⁅yamadaR₅ d t ⊔ yamadaR₆ d t, yamadaR₅ d t ⊔ yamadaR₆ d t⁆ := by
    rw [htinv, show t * (t * b * w * t) * t = (t * t) * b * w * (t * t) by group,
      h.t_mul_t] at h2
    simpa using h2
  have hwE := hF₃ (h.yamadaW₃_le_yamadaF₃ d hlay hw)
  have := mul_mem h3 (inv_mem hwE)
  rwa [mul_inv_cancel_right] at this

end Commutator

section Witness

theorem exists_mem_commutator_inf_yamadaM₄_QD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hS₄ : ⁅yamadaR₅ d t ⊔ yamadaR₆ d t, yamadaR₅ d t ⊔ yamadaR₆ d t⁆ ≤ yamadaS₄ d t) :
    ∃ u ∈ ⁅yamadaR₅ d t ⊔ yamadaR₆ d t, yamadaR₅ d t ⊔ yamadaR₆ d t⁆, u ∈ yamadaM₄ d t ∧
      ∃ α : G, u * t * u⁻¹ = t * α ∧ ∃ a : d.Γ, a ≠ 0 ∧ ∃ w ∈ yamadaW₃ d t,
        α = ((d.x₃ a : L) : G) * w := by
  layer_ctx
  have hx₁M₃ : ((d.x₁ 1 : L) : G) ∈ yamadaM₃ d t :=
    h.yamadaM_map_le_yamadaM₃_R5 d hlay ⟨d.x₁ 1, d.x₁_mem_M 1, rfl⟩
  have hsS : ((d.x₂ 1 : L) : G) ∈ d.S.map L.subtype :=
    ⟨d.x₂ 1, d.U₂_le_S (d.x₂_mem_U₂ 1), rfl⟩
  obtain ⟨n, hn, hxs⟩ : ∃ n ∈ d.W, ⁅d.x₁ 1, d.x₂ 1⁆ = d.x₃ (1 * ((1 : d.Γ₀) : d.Γ)) * n :=
    ⟨_, mul_mem (d.x₄_mem_W _) (d.x₅_mem_W _), by rw [d.comm₁₂, mul_assoc]⟩
  have hc : ((d.x₁ 1 : L) : G) * ((d.x₂ 1 : L) : G) * ((d.x₁ 1 : L) : G)⁻¹ *
      ((d.x₂ 1 : L) : G)⁻¹ = ((d.x₃ (1 * ((1 : d.Γ₀) : d.Γ)) : L) : G) * (n : G) := by
    have := congrArg (fun z : L => (z : G)) hxs
    simpa [commutatorElement_def] using this
  obtain ⟨y, hy₆, w₀, hw₀, hyt⟩ := h.exists_mem_yamadaL₆_conj_eq d hlay hx₁M₃
  have hym : y * t * y⁻¹ = t * (((d.x₁ 1 : L) : G) * w₀) := by rw [hyt, mul_assoc]
  have hst : ((d.x₂ 1 : L) : G) * t = t * ((d.x₂ 1 : L) : G) :=
    mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hsS)
  have hyE : y ∈ yamadaR₅ d t ⊔ yamadaR₆ d t := mem_sup_right (yamadaL₆_le_yamadaR₆ d t hy₆)
  have hsE : ((d.x₂ 1 : L) : G) ∈ yamadaR₅ d t ⊔ yamadaR₆ d t :=
    mem_sup_left (mem_sup_right hsS)
  have hu : y * ((d.x₂ 1 : L) : G) * y⁻¹ * ((d.x₂ 1 : L) : G)⁻¹ ∈
      ⁅yamadaR₅ d t ⊔ yamadaR₆ d t, yamadaR₅ d t ⊔ yamadaR₆ d t⁆ := by
    have := commutator_mem_commutator hyE hsE
    rwa [commutatorElement_def] at this
  have hu₄ := h.commutator_mem_yamadaL₄_of_mem_yamadaL₆_L6T d hlay hy₆ hsS
  have htM₄ : t ∈ normalizer (yamadaM₄ d t : Set G) :=
    h.yamadaR₄_le_normalizer_yamadaM₄_R4 d hlay (h.t_mem_yamadaR₄_QD d hlay)
  have huM : y * ((d.x₂ 1 : L) : G) * y⁻¹ * ((d.x₂ 1 : L) : G)⁻¹ ∈ yamadaM₄ d t := by
    have hL₄ : y * ((d.x₂ 1 : L) : G) * y⁻¹ * ((d.x₂ 1 : L) : G)⁻¹ ∈
        yamadaM₄ d t ⊔ zpowers t := by
      rw [← h524.1.1]
      exact hu₄
    rcases (h.mem_sup_zpowers_iff_of_normalizer htM₄).1 hL₄ with h1 | h1
    · exact h1
    · exfalso
      have h2 := mul_mem (mem_inf.1 (yamadaM₄_le_yamadaS₄_R4 d t h1)).2
        (inv_mem (mem_inf.1 (hS₄ hu)).2)
      rw [mul_inv_cancel_right] at h2
      exact h.t_not_mem_centralizer_yamadaV₁ d hlay h2
  have hκ := conj_commutator_t_eq_QD hym hst
  have hx₁N : ((d.x₁ 1 : L) : G) ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaL₃_le_normalizer_yamadaW₃ d hlay (mem_inf.1 hx₁M₃).1
  have hsN : ((d.x₂ 1 : L) : G) ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaR₄_le_normalizer_yamadaW₃_R4 d hlay (h.S_map_le_yamadaR₄_R4 d hlay hsS)
  have hyN : y ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.normalizer_yamadaL₃_le_normalizer_yamadaW₃ d hlay (yamadaL₆_le d t hy₆).1
  have hx₃F₃ : ((d.x₃ (1 * ((1 : d.Γ₀) : d.Γ)) : L) : G) ∈ yamadaF₃ d t :=
    h.F_map_le_yamadaF₃ d hlay ⟨d.x₃ _, d.x₃_mem_F _, rfl⟩
  have hx₃N : ((d.x₃ (1 * ((1 : d.Γ₀) : d.Γ)) : L) : G) ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaL₃_le_normalizer_yamadaW₃ d hlay (mem_inf.1 (mem_inf.1 hx₃F₃).1).1
  have hyT : y ∈ yamadaT₆ d t := h.yamadaL₆_le_yamadaT₆ d hlay hy₆
  have hw₀M₃ : w₀ ∈ yamadaM₃ d t :=
    (mem_inf.1 (h.yamadaW₃_le_yamadaF₃ d hlay hw₀)).1
  have hw₁ : y⁻¹ * (((d.x₁ 1 : L) : G) * w₀) * y * (((d.x₁ 1 : L) : G) * w₀)⁻¹ ∈
      yamadaW₃ d t := by
    have := h.commutator_mem_yamadaW₃_of_mem_yamadaT₆ d hlay (inv_mem hyT)
      (mul_mem hx₁M₃ hw₀M₃)
    rwa [inv_inv] at this
  have hw₅ : y * ((d.x₃ (1 * ((1 : d.Γ₀) : d.Γ)) : L) : G) * y⁻¹ *
      ((d.x₃ (1 * ((1 : d.Γ₀) : d.Γ)) : L) : G)⁻¹ ∈ yamadaW₃ d t :=
    h.commutator_mem_yamadaW₃_of_mem_yamadaT₆ d hlay hyT (mem_inf.1 hx₃F₃).1
  obtain ⟨w, hw, hwe⟩ := exists_conj_commutator_QD hx₁N hsN hyN hx₃N hw₀
    (h.W_map_le_yamadaW₃_S4C d hlay ⟨n, hn, rfl⟩) hc hw₁ hw₅
  exact ⟨_, hu, huM, _, hκ, 1 * ((1 : d.Γ₀) : d.Γ), by simp, w, hw, hwe⟩

end Witness

section Irreducible

theorem inv_mul_mem_yamadaM₃_QD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {m₁ m₂ a₁ a₂ : G} (hm₁ : m₁ ∈ yamadaM₄ d t) (hm₂ : m₂ ∈ yamadaM₄ d t)
    (h₁ : m₁ * t * m₁⁻¹ = t * a₁) (h₂ : m₂ * t * m₂⁻¹ = t * a₂)
    (ha : a₁⁻¹ * a₂ ∈ yamadaW₃ d t) : m₁⁻¹ * m₂ ∈ yamadaM₃ d t := by
  have hm₁N : m₁ ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaR₄_le_normalizer_yamadaW₃_R4 d hlay ((inf_le_left : yamadaM₄ d t ≤ yamadaR₄ d t) hm₁)
  have hm₂N : m₂ ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaR₄_le_normalizer_yamadaW₃_R4 d hlay ((inf_le_left : yamadaM₄ d t ≤ yamadaR₄ d t) hm₂)
  have htW₃ : t ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaL₃_le_normalizer_yamadaW₃ d hlay (h.t_mem_yamadaL₃_L6T d hlay)
  have hL₆ : ∀ m ∈ yamadaM₄ d t, m ∈ yamadaL₆ d t := fun m hm =>
    (yamadaM₆_le_yamadaL₆ d t) (h.yamadaM₄_le_yamadaM₆ d hlay hm)
  have hq := conj_quotient_t_eq_QD h₂ h₁
  have hK : m₁⁻¹ * m₂ ∈ normalizer ((yamadaW₃ d t ⊔ zpowers t : Subgroup G) : Set G) :=
    h.mem_normalizer_sup_zpowers_D3 htW₃ (mul_mem (inv_mem hm₁N) hm₂N) (by
      rw [hq]
      exact mul_mem (mem_sup_right (mem_zpowers t))
        (mem_sup_left (inv_conj_mem_QD hm₁N ha)))
  have hL₃ : m₁⁻¹ * m₂ ∈ yamadaL₃ d t := by
    rw [← h.yamadaL₆_inf_normalizer d hlay]
    exact mem_inf.2 ⟨mul_mem (inv_mem (hL₆ m₁ hm₁)) (hL₆ m₂ hm₂), hK⟩
  exact mem_inf.2 ⟨hL₃, mul_mem
    (inv_mem ((inf_le_right : yamadaM₄ d t ≤ centralizer (yamadaY₂ d t : Set G)) hm₁))
    ((inf_le_right : yamadaM₄ d t ≤ centralizer (yamadaY₂ d t : Set G)) hm₂)⟩

theorem yamadaM₄_le_commutator_QD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hS₄ : ⁅yamadaR₅ d t ⊔ yamadaR₆ d t, yamadaR₅ d t ⊔ yamadaR₆ d t⁆ ≤ yamadaS₄ d t)
    (hF₃ : yamadaF₃ d t = d.F.map L.subtype ⊔ yamadaW₃ d t) :
    yamadaM₄ d t ≤ ⁅yamadaR₅ d t ⊔ yamadaR₆ d t, yamadaR₅ d t ⊔ yamadaR₆ d t⁆ := by
  layer_ctx
  obtain ⟨u, hu, huM, α₀, hut, a₀, ha₀, w₀, hw₀, hα₀⟩ :=
    h.exists_mem_commutator_inf_yamadaM₄_QD d hlay hS₄
  have hM₃E := h.yamadaM₃_le_commutator_QD d hlay
  intro m hm
  have hmL₄ : m ∈ yamadaL₄ d t := by
    rw [h524.1.1]
    exact mem_sup_left hm
  obtain ⟨α, hα, hmt⟩ := h.exists_conj_t_eq_mul_of_mem_yamadaL₄ d hlay hmL₄
  obtain ⟨b, w₂, hw₂, hαb⟩ : ∃ b : d.Γ, ∃ w₂ ∈ yamadaW₃ d t,
      α = ((d.x₃ b : L) : G) * w₂ := by
    have hFN : d.F.map L.subtype ≤ normalizer (yamadaW₃ d t : Set G) := fun g hg =>
      h.yamadaR₄_le_normalizer_yamadaW₃_R4 d hlay
        (h.S_map_le_yamadaR₄_R4 d hlay (map_mono d.F_le_S hg))
    rw [hF₃, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hFN, Set.mem_mul] at hα
    obtain ⟨f₁, ⟨f₀, hf₀, rfl⟩, w₁, hw₁, e⟩ := hα
    obtain ⟨b, n, hn, rfl⟩ := d.mem_F_iff.1 hf₀
    refine ⟨b, ((n : L) : G) * w₁, mul_mem (h.W_map_le_yamadaW₃_S4C d hlay ⟨n, hn, rfl⟩) hw₁, ?_⟩
    rw [← e]
    simp [mul_assoc]
  by_cases hb : b = 0
  ·
    have hαW : (1 : G)⁻¹ * α ∈ yamadaW₃ d t := by
      rw [hαb, hb, d.x₃_zero]
      simpa using hw₂
    have h1 := h.inv_mul_mem_yamadaM₃_QD d hlay (one_mem _) hm (a₁ := 1) (by simp) hmt hαW
    exact hM₃E (by simpa using h1)
  · have hx₃a : d.x₃ a₀ ≠ 1 := fun e => ha₀ (d.x₃_injective (e.trans d.x₃_zero.symm))
    have hx₃b : d.x₃ b ≠ 1 := fun e => hb (d.x₃_injective (e.trans d.x₃_zero.symm))
    obtain ⟨j, ⟨hj, hjx⟩, -⟩ := (d.yamada_three_five_five.2.1).2 _ (d.x₃_mem_U₃ a₀) hx₃a _
      (d.x₃_mem_U₃ b) hx₃b
    have hjx' : (j : G) * ((d.x₃ a₀ : L) : G) * (j : G)⁻¹ = ((d.x₃ b : L) : G) := by
      have := congrArg (fun z : L => (z : G)) hjx
      simpa using this
    have hjt : (j : G) * t = t * j := mem_centralizer_singleton_iff.1 (h.L_le_centralizer j.2)
    have hjt' : (j : G)⁻¹ * t * j = t := by rw [mul_assoc, ← hjt, inv_mul_cancel_left]
    have hjNCS : (j : G) ∈ centralizer ({t} : Set G) ⊓
        normalizer ((d.S.map L.subtype : Subgroup G) : Set G) :=
      ⟨h.L_le_centralizer j.2, map_le_normalizer_map d.J_le_normalizer_S
        ⟨j, (inf_le_left : d.J₂ ≤ d.J) hj, rfl⟩⟩
    have hjE : (j : G) ∈ normalizer ((yamadaR₅ d t ⊔ yamadaR₆ d t : Subgroup G) : Set G) :=
      Common.mem_normalizer_sup (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₅ d hjNCS)
        (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₆ d hlay hjNCS)
    have hjQ : (j : G) ∈ normalizer
        ((⁅yamadaR₅ d t ⊔ yamadaR₆ d t, yamadaR₅ d t ⊔ yamadaR₆ d t⁆ : Subgroup G) : Set G) :=
      normalizer_le_normalizer_commutator_C8 _ hjE
    have hjR₄ := h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₄ d hlay hjNCS
    have hjN := h.normalizer_yamadaR₄_le_of_layerHyp d hlay hjR₄
    have hjM₄ : (j : G) ∈ normalizer (yamadaM₄ d t : Set G) :=
      Common.mem_normalizer_inf hjR₄ (mem_normalizer_centralizer_C8 hjN.2)
    have hjW₃ : (j : G) ∈ normalizer (yamadaW₃ d t : Set G) := hjN.1.2
    have hu'Q : (j : G) * u * (j : G)⁻¹ ∈
        ⁅yamadaR₅ d t ⊔ yamadaR₆ d t, yamadaR₅ d t ⊔ yamadaR₆ d t⁆ :=
      (mem_normalizer_iff.1 hjQ u).1 hu
    have hu'M : (j : G) * u * (j : G)⁻¹ ∈ yamadaM₄ d t := (mem_normalizer_iff.1 hjM₄ u).1 huM
    have hu't : (j : G) * u * (j : G)⁻¹ * t * ((j : G) * u * (j : G)⁻¹)⁻¹ =
        t * ((j : G) * α₀ * (j : G)⁻¹) := by
      calc (j : G) * u * (j : G)⁻¹ * t * ((j : G) * u * (j : G)⁻¹)⁻¹
          = (j : G) * (u * ((j : G)⁻¹ * t * j) * u⁻¹) * (j : G)⁻¹ := by group
        _ = (j : G) * (u * t * u⁻¹) * (j : G)⁻¹ := by rw [hjt']
        _ = (j : G) * (t * α₀) * (j : G)⁻¹ := by rw [hut]
        _ = ((j : G) * t) * α₀ * (j : G)⁻¹ := by group
        _ = t * ((j : G) * α₀ * (j : G)⁻¹) := by rw [hjt]; group
    have hwj : (j : G) * w₀ * (j : G)⁻¹ ∈ yamadaW₃ d t := (mem_normalizer_iff.1 hjW₃ w₀).1 hw₀
    have ha₁ : ((j : G) * α₀ * (j : G)⁻¹)⁻¹ * α ∈ yamadaW₃ d t := by
      have e : ((j : G) * α₀ * (j : G)⁻¹)⁻¹ * α = ((j : G) * w₀ * (j : G)⁻¹)⁻¹ * w₂ := by
        rw [hα₀, hαb]
        calc ((j : G) * (((d.x₃ a₀ : L) : G) * w₀) * (j : G)⁻¹)⁻¹ * (((d.x₃ b : L) : G) * w₂)
            = ((j : G) * w₀ * (j : G)⁻¹)⁻¹ *
              (((j : G) * ((d.x₃ a₀ : L) : G) * (j : G)⁻¹)⁻¹ * ((d.x₃ b : L) : G)) * w₂ := by
              group
          _ = ((j : G) * w₀ * (j : G)⁻¹)⁻¹ * w₂ := by rw [hjx', inv_mul_cancel, mul_one]
      rw [e]
      exact mul_mem (inv_mem hwj) hw₂
    have h1 := h.inv_mul_mem_yamadaM₃_QD d hlay hu'M hm hu't hmt ha₁
    have h2 := mul_mem hu'Q (hM₃E h1)
    rwa [mul_inv_cancel_left] at h2

end Irreducible

theorem yamadaF₃_eq_sup_map_F_QD (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) (hF₃ : yamadaF₃ d t = yamadaF₁ d t ⊔ yamadaW₃ d t) :
    yamadaF₃ d t = d.F.map L.subtype ⊔ yamadaW₃ d t := by
  layer_ctx
  have hV₁ := h.yamadaV₁_le_yamadaW₃_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102
  rw [hF₃, h.yamadaF₁_eq_sup d h561 h562]
  exact le_antisymm (sup_le (sup_le le_sup_left (hV₁.trans le_sup_right)) le_sup_right)
    (sup_le (le_sup_left.trans le_sup_left) le_sup_right)

theorem commutator_yamadaR₅_sup_yamadaR₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hker : (yamadaR₅ d t ⊔ yamadaR₆ d t) ⊓
      normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G) = yamadaR₄ d t)
    (hS₄c : ∀ x ∈ yamadaS₄ d t, ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaF₄ d t)
    (htS₄ : ∀ x ∈ yamadaS₄ d t, t * x * t * x⁻¹ ∈ yamadaF₄ d t)
    (hKF : normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaD₄ d t : Set G) ⊓
      normalizer (yamadaF₄ d t : Set G))
    (hM₄ : yamadaM₄ d t = d.M.map L.subtype ⊔ yamadaF₄ d t)
    (hF₃ : yamadaF₃ d t = d.F.map L.subtype ⊔ yamadaW₃ d t) :
    ⁅yamadaR₅ d t ⊔ yamadaR₆ d t, yamadaR₅ d t ⊔ yamadaR₆ d t⁆ = yamadaS₄ d t := by
  have hEC := h.sup_le_modCentralizerSub_QD d hlay hS₄c htS₄ hKF hM₄
  have hS₄ := h.commutator_sup_le_yamadaS₄_QD d hlay hker hS₄c (hKF.trans inf_le_right) hEC
  refine le_antisymm hS₄ ?_
  rw [h.yamadaS₄_eq_sup d hlay]
  exact sup_le (h.yamadaM₄_le_commutator_QD d hlay hS₄ hF₃) (h.yamadaD₁_le_commutator_QD d hlay)

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
