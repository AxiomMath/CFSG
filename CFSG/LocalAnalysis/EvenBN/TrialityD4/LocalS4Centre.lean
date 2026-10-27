module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalR4
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Ten

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open scoped commutatorElement Pointwise

section Generic

variable {G : Type*} [Group G]

theorem comm_mem_of_mul_comm_mem_S4C {A : Subgroup G} {a b y : G}
    (ha : a ∈ normalizer (A : Set G)) (h1 : a * b * y * (a * b)⁻¹ * y⁻¹ ∈ A)
    (h2 : a * y * a⁻¹ * y⁻¹ ∈ A) : b * y * b⁻¹ * y⁻¹ ∈ A := by
  have h3 : a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ ∈ A := by
    have := mul_mem h1 (inv_mem h2)
    rwa [show a * b * y * (a * b)⁻¹ * y⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ =
      a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ by group] at this
  have h4 := (mem_normalizer_iff.1 (inv_mem ha) _).1 h3
  rwa [show a⁻¹ * (a * (b * y * b⁻¹ * y⁻¹) * a⁻¹) * a⁻¹⁻¹ = b * y * b⁻¹ * y⁻¹ by group] at h4

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
  have h515 := h.yamada_5_15 d hNH h561 h562 h591 h592 h593
  have h524 := h.yamada_5_24 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221
  have h525 := h.yamada_5_25 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521))

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

section Basic

theorem yamadaS₁_le_yamadaS₄_S4C (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaS₁ d t ≤ yamadaS₄ d t :=
  sup_le (h.S_map_le_yamadaS₄_R4 d hlay) (h.yamadaD₁_le_yamadaS₄_R4 d hlay)

theorem yamadaS₂_le_yamadaS₄_S4C (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaS₂ d t ≤ yamadaS₄ d t :=
  sup_le (h.S_map_le_yamadaS₄_R4 d hlay)
    ((h.yamadaY₂_le_yamadaM₄_R4 d hlay).trans (yamadaM₄_le_yamadaS₄_R4 d t))

theorem yamadaV₁_le_yamadaS₄_S4C (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaV₁ d t ≤ yamadaS₄ d t :=
  (yamadaV₁_le_yamadaD₁ d t).trans (h.yamadaD₁_le_yamadaS₄_R4 d hlay)

theorem yamadaS₁_le_yamadaS₂_S4C (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaS₁ d t ≤ yamadaS₂ d t := by
  rw [h.yamadaS₁_eq_sup d hlay]
  exact sup_le le_sup_left ((yamadaV₁_le_yamadaY₂ d).trans le_sup_right)

theorem yamadaW₂_le_yamadaW₃_S4C (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaW₂ d t ≤ yamadaW₃ d t := by
  rw [← h.yamadaM₂_inf_yamadaW₃ d hlay]
  exact inf_le_right

theorem W_map_le_yamadaW₃_S4C (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : d.W.map L.subtype ≤ yamadaW₃ d t :=
  (le_sup_left : d.W.map L.subtype ≤ yamadaW₂ d t).trans (h.yamadaW₂_le_yamadaW₃_S4C d hlay)

theorem yamadaW₃_le_yamadaD₅_S4C (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaW₃ d t ≤ yamadaD₅ d t := fun w hw =>
  mem_inf.2 ⟨h.yamadaW₃_le_yamadaC₅ d hlay hw,
    (mem_inf.1 (h.yamadaW₃_le_yamadaS₄_R4 d hlay hw)).2⟩

theorem yamadaD₁_le_yamadaD₄_S4C (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaD₁ d t ≤ yamadaD₄ d t :=
  le_inf (h.yamadaD₁_le_yamadaR₄_R4 d hlay)
    (le_inf ((h.yamadaD₁_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t))
      (yamadaD₁_le_centralizer_yamadaV₁ d))

theorem F_map_le_yamadaF₄_S4C (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : d.F.map L.subtype ≤ yamadaF₄ d t := by
  have hFR₄ : d.F.map L.subtype ≤ yamadaR₄ d t :=
    (map_mono d.F_le_S).trans (h.S_map_le_yamadaR₄_R4 d hlay)
  have hFD₁ : d.F.map L.subtype ≤ yamadaD₁ d t :=
    (map_mono d.F_le_D).trans (D_le_yamadaD₁ d t)
  exact le_inf (le_inf hFR₄ ((map_mono d.F_le_M).trans
    (h.M_map_le_centralizer_yamadaY₂ d hlay))) (hFD₁.trans (h.yamadaD₁_le_yamadaD₄_S4C d hlay))

theorem yamadaF₄_le_yamadaS₄_S4C {q : ℕ} (d : TrialityD4Data L q) (t : G) :
    yamadaF₄ d t ≤ yamadaS₄ d t :=
  (yamadaF₄_le_yamadaM₄ d t).trans (yamadaM₄_le_yamadaS₄_R4 d t)

theorem S_map_le_normalizer_yamadaF₄_S4C (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : d.S.map L.subtype ≤ normalizer (yamadaF₄ d t : Set G) := by
  layer_ctx
  intro s hs
  have hsR₄ : s ∈ yamadaR₄ d t := h.S_map_le_yamadaR₄_R4 d hlay hs
  have hsC₅ : s ∈ normalizer (yamadaC₅ d t : Set G) :=
    le_normalizer_yamadaC₅ d t (h.S_le_normalizer_yamadaC₁ d hs)
  have hsV₁ : s ∈ normalizer (centralizer (yamadaV₁ d t : Set G) : Set G) :=
    mem_normalizer_centralizer_C8 (S_le_normalizer_yamadaV₁ d h593 hs)
  exact Common.mem_normalizer_inf (h.yamadaR₄_le_normalizer_yamadaM₄_R4 d hlay hsR₄)
    (Common.mem_normalizer_inf (le_normalizer hsR₄) (Common.mem_normalizer_inf hsC₅ hsV₁))

end Basic

section Commutators

theorem mem_yamadaS₂_of_commutator_mem_S4C (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {A : Subgroup G} (hA : A ≤ yamadaS₁ d t) {x : G}
    (hx : x ∈ yamadaS₄ d t) (hc : ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ A) :
    x ∈ yamadaS₂ d t := by
  layer_ctx
  have hS₁ := h.yamadaS₁_le_yamadaS₄_S4C d hlay
  obtain ⟨hxR₄, hxC⟩ := mem_inf.1 hx
  have hx' : x ∈ yamadaR₅ d t ⊓ normalizer (yamadaS₁ d t : Set G) := by
    refine mem_inf.2 ⟨h514.2.2.2.2.2.1 hxR₄, mem_normalizer_fintype fun s hs => ?_⟩
    have := mul_mem (hA (hc s (hS₁ hs))) hs
    rwa [show x * s * x⁻¹ * s⁻¹ * s = x * s * x⁻¹ by group] at this
  rw [h515.1] at hx'
  have htS₂ : t ∈ normalizer (yamadaS₂ d t : Set G) :=
    mem_normalizer_sup (h.t_mem_normalizer_map_D1 d.S) (h.t_mem_normalizer_yamadaY₂_D1 d)
  rw [h591.2.2.1, h.mem_sup_zpowers_iff_of_normalizer htS₂] at hx'
  rcases hx' with h1 | h1
  · exact h1
  · exfalso
    have h3 : t * x ∈ centralizer (yamadaV₁ d t : Set G) :=
      h.yamadaS₂_le_centralizer_yamadaV₁ d hlay h1
    have := mul_mem h3 (inv_mem hxC)
    rw [mul_inv_cancel_right] at this
    exact h.t_not_mem_centralizer_yamadaV₁ d hlay this

theorem mem_yamadaR₃_of_commutator_mem_S4C (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} (hx : x ∈ yamadaS₄ d t)
    (hc : ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaY₂ d t) : x ∈ yamadaR₃ d t := by
  layer_ctx
  have hS₂ := h.yamadaS₂_le_yamadaS₄_S4C d hlay
  have hxR₄ : x ∈ yamadaR₄ d t := (mem_inf.1 hx).1
  have hxS₂ : x ∈ normalizer (yamadaS₂ d t : Set G) := by
    refine mem_normalizer_fintype fun s hs => ?_
    have := mul_mem ((le_sup_right : yamadaY₂ d t ≤ yamadaS₂ d t) (hc s (hS₂ hs))) hs
    rwa [show x * s * x⁻¹ * s⁻¹ * s = x * s * x⁻¹ by group] at this
  have htS₂ : t ∈ normalizer (yamadaS₂ d t : Set G) :=
    mem_normalizer_sup (h.t_mem_normalizer_map_D1 d.S) (h.t_mem_normalizer_yamadaY₂_D1 d)
  obtain ⟨w, hwF₁, hw⟩ := h514.2.1.1 x hxR₄
  have hwS₂ : w ∈ yamadaS₂ d t :=
    h.yamadaS₁_le_yamadaS₂_S4C d hlay ((le_sup_right : yamadaD₁ d t ≤ yamadaS₁ d t)
      (yamadaF₁_le_yamadaD₁ d hwF₁))
  have hgt : x * t * x⁻¹ ∈ yamadaS₂ d t ⊔ zpowers t := by
    rw [hw]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hwS₂)
  have hxR₂ : x ∈ normalizer (yamadaR₂ d t : Set G) := by
    rw [h591.2.2.1]
    exact h.mem_normalizer_sup_zpowers_D3 htS₂ hxS₂ hgt
  have hxV₂ := (mem_inf.1 (normalizer_yamadaR₂_le d h592 h5101 h5102 hxR₂)).1
  exact (h.mem_yamadaR₃_iff_of_mem_yamadaR₄ d hNH h561 h562 h591 h592 h593 hxR₄).2
    ((le_sup_left : d.W.map L.subtype ≤ yamadaW₁ d t) (h.crossed_mem_W d h562 h592 hxV₂))

theorem exists_mul_of_mem_yamadaR₃_S4C (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} (hx : x ∈ yamadaR₃ d t)
    (hxC : x ∈ centralizer (yamadaV₁ d t : Set G)) :
    ∃ w ∈ yamadaW₃ d t, ∃ s ∈ d.S.map L.subtype, x = w * s := by
  layer_ctx
  have hx' : x ∈ ((yamadaR₃ d t : Subgroup G) : Set G) := hx
  rw [h.coe_yamadaR₃_eq_mul d hlay] at hx'
  obtain ⟨z, hz, s, hs, e⟩ := Set.mem_mul.1 hx'
  have hz' : z ∈ yamadaW₃ d t ⊔ zpowers t := hz
  have htW₃ : t ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.t_mem_normalizer_yamadaW₃_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102
  rw [h.mem_sup_zpowers_iff_of_normalizer htW₃] at hz'
  rcases hz' with h1 | h1
  · exact ⟨z, h1, s, hs, e.symm⟩
  · exfalso
    have hsC : s ∈ centralizer (yamadaV₁ d t : Set G) := h.S_map_le_centralizer_yamadaV₁ d hlay hs
    have hzC : z ∈ centralizer (yamadaV₁ d t : Set G) := by
      have := mul_mem hxC (inv_mem hsC)
      rwa [← e, mul_inv_cancel_right] at this
    have htzC : t * z ∈ centralizer (yamadaV₁ d t : Set G) :=
      (mem_inf.1 (h.yamadaW₃_le_yamadaS₄_R4 d hlay h1)).2
    have := mul_mem htzC (inv_mem hzC)
    rw [mul_inv_cancel_right] at this
    exact h.t_not_mem_centralizer_yamadaV₁ d hlay this

theorem commutator_mem_yamadaV₁_of_mem_yamadaS₄_S4C (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {s y : G} (hs : s ∈ yamadaS₄ d t)
    (hy : y ∈ yamadaY₂ d t) : s * y * s⁻¹ * y⁻¹ ∈ yamadaV₁ d t := by
  layer_ctx
  have hK : ∀ g ∈ yamadaS₄ d t, ∀ z ∈ yamadaY₂ d t, g * z * g⁻¹ ∈ yamadaY₂ d t :=
    fun g hg z hz => (mem_normalizer_iff.1
      (h.yamadaR₄_le_normalizer_yamadaY₂_R4 d hlay (mem_inf.1 hg).1) z).1 hz
  have hB : ∀ g ∈ yamadaS₄ d t, ∀ b ∈ yamadaV₁ d t, g * b * g⁻¹ ∈ yamadaV₁ d t :=
    fun g hg b hb => by
      rw [show g * b * g⁻¹ = b by
        rw [← mem_centralizer_iff.1 (mem_inf.1 hg).2 b hb, mul_inv_cancel_right]]
      exact hb
  have hle : yamadaM₄ d t ⊔ yamadaD₁ d t ≤
      Common.centralizerMod (yamadaS₄ d t) (yamadaY₂ d t) (yamadaV₁ d t) hK hB := by
    refine sup_le (fun m hm => ⟨yamadaM₄_le_yamadaS₄_R4 d t hm, fun z hz => ?_⟩)
      (fun δ hδ => ⟨h.yamadaD₁_le_yamadaS₄_R4 d hlay hδ, fun z hz => ?_⟩)
    · exact mem_of_mul_comm_R4 (mem_centralizer_iff.1 (mem_inf.1 hm).2 z hz).symm
    · have hδD₅ : δ ∈ yamadaD₅ d t :=
        mem_inf.2 ⟨(h.yamadaD₁_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t) hδ,
          yamadaD₁_le_centralizer_yamadaV₁ d hδ⟩
      have hzD₅ : z ∈ yamadaD₅ d t := h.yamadaW₃_le_yamadaD₅_S4C d hlay
        (h.yamadaW₂_le_yamadaW₃_S4C d hlay ((le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) hz))
      have := commutator_mem_commutator hδD₅ hzD₅
      rw [h525.1] at this
      exact this
  exact (Common.mem_centralizerMod.1 (hle ((h.yamadaS₄_eq_sup d hlay).le hs))).2 y hy

end Commutators

section Series

theorem mem_yamadaV₁_iff_S4C (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} :
    x ∈ yamadaV₁ d t ↔ x ∈ yamadaS₄ d t ∧
      ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ (⊥ : Subgroup G) := by
  constructor
  · intro hx
    exact ⟨h.yamadaV₁_le_yamadaS₄_S4C d hlay hx, fun y hy =>
      mem_of_mul_comm_R4 (mem_centralizer_iff.1 (mem_inf.1 hy).2 x hx)⟩
  · rintro ⟨hx, hc⟩
    have hS₂ := h.yamadaS₂_le_yamadaS₄_S4C d hlay
    have hxS₂ := h.mem_yamadaS₂_of_commutator_mem_S4C d hlay bot_le hx hc
    rw [← h.yamadaS₂_inf_centralizer d hlay]
    exact mem_inf.2 ⟨hxS₂, mem_centralizer_iff.2 fun s hs =>
      (mul_comm_of_comm_mem_bot_R4 (hc s (hS₂ hs))).symm⟩

theorem mem_yamadaY₂_iff_S4C (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} :
    x ∈ yamadaY₂ d t ↔ x ∈ yamadaS₄ d t ∧
      ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaV₁ d t := by
  constructor
  · intro hx
    exact ⟨(h.yamadaS₂_le_yamadaS₄_S4C d hlay) ((le_sup_right : yamadaY₂ d t ≤ yamadaS₂ d t) hx),
      fun y hy => comm_swap_mem_R4
        (h.commutator_mem_yamadaV₁_of_mem_yamadaS₄_S4C d hlay hy hx)⟩
  · rintro ⟨hx, hc⟩
    have hV₁S₁ : yamadaV₁ d t ≤ yamadaS₁ d t :=
      (yamadaV₁_le_yamadaD₁ d t).trans le_sup_right
    have hxS₂ := h.mem_yamadaS₂_of_commutator_mem_S4C d hlay hV₁S₁ hx hc
    exact (h.mem_yamadaY₂_iff d hlay).2 ⟨hxS₂, fun y hy =>
      hc y (h.yamadaS₂_le_yamadaS₄_S4C d hlay hy)⟩

theorem mem_yamadaW₃_iff_S4C (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hM₄ : ∀ m ∈ yamadaM₄ d t, ∀ w ∈ yamadaW₃ d t, m * w * m⁻¹ * w⁻¹ ∈ yamadaY₂ d t)
    {x : G} :
    x ∈ yamadaW₃ d t ↔ x ∈ yamadaS₄ d t ∧
      ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaY₂ d t := by
  constructor
  · intro hx
    exact ⟨h.yamadaW₃_le_yamadaS₄_R4 d hlay hx, fun y hy =>
      comm_swap_mem_R4 (h.commutator_mem_yamadaY₂_of_mem_yamadaS₄ d hlay hM₄ hy hx)⟩
  · rintro ⟨hx, hc⟩
    have h592 := h.yamada_5_9_2 d hlay
    have hxR₃ := h.mem_yamadaR₃_of_commutator_mem_S4C d hlay hx hc
    obtain ⟨w, hw, s, hs, rfl⟩ :=
      h.exists_mul_of_mem_yamadaR₃_S4C d hlay hxR₃ (mem_inf.1 hx).2
    obtain ⟨s₀, hs₀, hs₀e⟩ := hs
    have hs₀e' : ((s₀ : L) : G) = s := hs₀e
    subst hs₀e'
    have hs₀W : s₀ ∈ d.W := by
      refine d.mem_W_iff_forall.2 ⟨hs₀, fun y₀ hy₀ => ?_⟩
      have hy : ((y₀ : L) : G) ∈ yamadaS₄ d t :=
        h.S_map_le_yamadaS₄_R4 d hlay ⟨y₀, hy₀, rfl⟩
      have h3 := comm_mem_of_mul_comm_mem_S4C (A := yamadaY₂ d t) (b := (s₀ : G))
        (h.yamadaR₄_le_normalizer_yamadaY₂_R4 d hlay (h.yamadaW₃_le_yamadaR₄_R4 d hlay hw))
        (hc _ hy) (comm_swap_mem_R4
          (h.commutator_mem_yamadaY₂_of_mem_yamadaS₄ d hlay hM₄ hy hw))
      have h4 : ((⁅s₀, y₀⁆ : L) : G) ∈ yamadaY₂ d t ⊓ centralizer ({t} : Set G) := by
        refine mem_inf.2 ⟨?_, h.L_le_centralizer (⁅s₀, y₀⁆ : L).2⟩
        have e : ((⁅s₀, y₀⁆ : L) : G) = (s₀ : G) * y₀ * (s₀ : G)⁻¹ * (y₀ : G)⁻¹ := by
          rw [commutatorElement_def]
          simp
        rw [e]
        exact h3
      rw [h592.2.2.2.2] at h4
      obtain ⟨y, hy', hye⟩ := h4
      rw [Subtype.ext hye] at hy'
      exact hy'
    exact mul_mem hw (h.W_map_le_yamadaW₃_S4C d hlay ⟨s₀, hs₀W, rfl⟩)

theorem mem_yamadaF₄_iff_S4C (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hF₄ : ∀ x ∈ yamadaF₄ d t, ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaW₃ d t)
    (hS₄ : yamadaS₄ d t = yamadaF₄ d t ⊔ d.S.map L.subtype) {x : G} :
    x ∈ yamadaF₄ d t ↔ x ∈ yamadaS₄ d t ∧
      ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaW₃ d t := by
  constructor
  · intro hx
    exact ⟨yamadaF₄_le_yamadaS₄_S4C d t hx, hF₄ x hx⟩
  · rintro ⟨hx, hc⟩
    have hx' : x ∈ ((yamadaF₄ d t ⊔ d.S.map L.subtype : Subgroup G) : Set G) := by
      rw [← hS₄]
      exact hx
    rw [coe_mul_of_right_le_normalizer_left _ _ (h.S_map_le_normalizer_yamadaF₄_S4C d hlay)] at hx'
    obtain ⟨f₀, hf₀, s, hs, e⟩ := Set.mem_mul.1 hx'
    have hf₀' : f₀ ∈ yamadaF₄ d t := hf₀
    obtain ⟨s₀, hs₀, hs₀e⟩ := hs
    have hs₀e' : ((s₀ : L) : G) = s := hs₀e
    subst hs₀e'
    have hs₀F : s₀ ∈ d.F := by
      refine d.mem_F_iff_forall.2 ⟨hs₀, fun y₀ hy₀ => ?_⟩
      have hy : ((y₀ : L) : G) ∈ yamadaS₄ d t :=
        h.S_map_le_yamadaS₄_R4 d hlay ⟨y₀, hy₀, rfl⟩
      have hf₀R₄ : f₀ ∈ yamadaR₄ d t :=
        (mem_inf.1 (yamadaF₄_le_yamadaS₄_S4C d t hf₀')).1
      have h1 : f₀ * (s₀ : G) * (y₀ : G) * (f₀ * (s₀ : G))⁻¹ * (y₀ : G)⁻¹ ∈ yamadaW₃ d t := by
        rw [e]
        exact hc _ hy
      have h3 := comm_mem_of_mul_comm_mem_S4C (A := yamadaW₃ d t)
        (h.yamadaR₄_le_normalizer_yamadaW₃_R4 d hlay hf₀R₄) h1 (hF₄ f₀ hf₀' _ hy)
      have h4 : ((⁅s₀, y₀⁆ : L) : G) ∈ yamadaW₃ d t ⊓ centralizer ({t} : Set G) := by
        refine mem_inf.2 ⟨?_, h.L_le_centralizer (⁅s₀, y₀⁆ : L).2⟩
        have e' : ((⁅s₀, y₀⁆ : L) : G) = (s₀ : G) * y₀ * (s₀ : G)⁻¹ * (y₀ : G)⁻¹ := by
          rw [commutatorElement_def]
          simp
        rw [e']
        exact h3
      obtain ⟨y, hy', hye⟩ := h.yamadaW₃_inf_centralizer_le d hlay h4
      rw [Subtype.ext hye] at hy'
      exact hy'
    rw [← e]
    exact mul_mem hf₀' (h.F_map_le_yamadaF₄_S4C d hlay ⟨s₀, hs₀F, rfl⟩)

end Series

section Normalizer

theorem normalizer_yamadaS₄_le_two (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    normalizer (yamadaS₄ d t : Set G) ≤
      normalizer (yamadaV₁ d t : Set G) ⊓ normalizer (yamadaY₂ d t : Set G) := by
  intro g hg
  have hg₀ : g ∈ normalizer ((⊥ : Subgroup G) : Set G) :=
    mem_normalizer_fintype fun x hx => by
      rw [mem_bot.1 hx, mul_one, mul_inv_cancel]
      exact one_mem _
  have hgV : g ∈ normalizer (yamadaV₁ d t : Set G) :=
    mem_normalizer_of_forall_mem_iff_R4 hg hg hg₀ fun x => h.mem_yamadaV₁_iff_S4C d hlay
  exact mem_inf.2 ⟨hgV, mem_normalizer_of_forall_mem_iff_R4 hg hg hgV
    fun x => h.mem_yamadaY₂_iff_S4C d hlay⟩

theorem normalizer_yamadaS₄_le_three (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hM₄ : ∀ m ∈ yamadaM₄ d t, ∀ w ∈ yamadaW₃ d t, m * w * m⁻¹ * w⁻¹ ∈ yamadaY₂ d t) :
    normalizer (yamadaS₄ d t : Set G) ≤
      normalizer (yamadaV₁ d t : Set G) ⊓ normalizer (yamadaY₂ d t : Set G) ⊓
        normalizer (yamadaW₃ d t : Set G) := by
  intro g hg
  obtain ⟨hgV, hgY₂⟩ := mem_inf.1 (h.normalizer_yamadaS₄_le_two d hlay hg)
  exact mem_inf.2 ⟨mem_inf.2 ⟨hgV, hgY₂⟩, mem_normalizer_of_forall_mem_iff_R4 hg hg hgY₂
    fun x => h.mem_yamadaW₃_iff_S4C d hlay hM₄⟩

theorem normalizer_yamadaS₄_le (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hM₄ : ∀ m ∈ yamadaM₄ d t, ∀ w ∈ yamadaW₃ d t, m * w * m⁻¹ * w⁻¹ ∈ yamadaY₂ d t)
    (hF₄ : ∀ x ∈ yamadaF₄ d t, ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaW₃ d t)
    (hS₄ : yamadaS₄ d t = yamadaF₄ d t ⊔ d.S.map L.subtype) :
    normalizer (yamadaS₄ d t : Set G) ≤
      normalizer (yamadaV₁ d t : Set G) ⊓ normalizer (yamadaY₂ d t : Set G) ⊓
        normalizer (yamadaW₃ d t : Set G) ⊓ normalizer (yamadaF₄ d t : Set G) := by
  intro g hg
  obtain ⟨hgVY, hgW₃⟩ := mem_inf.1 (h.normalizer_yamadaS₄_le_three d hlay hM₄ hg)
  exact mem_inf.2 ⟨mem_inf.2 ⟨hgVY, hgW₃⟩, mem_normalizer_of_forall_mem_iff_R4 hg hg hgW₃
    fun x => h.mem_yamadaF₄_iff_S4C d hlay hF₄ hS₄⟩

end Normalizer

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
