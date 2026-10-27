module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL3Four

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open scoped commutatorElement Pointwise

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem mem_M_or_mem_D_of_mul_self_mem_W {s : X} (hs : s ∈ d.S) (h : s * s ∈ d.W) :
    s ∈ d.M ∨ s ∈ d.D := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff.1 hs
  obtain ⟨b, n', hn', rfl⟩ := d.mem_D_iff.1 hn
  obtain ⟨c, w₀, hw₀, rfl⟩ := d.mem_F_iff.1 hn'
  have hWN : ∀ g ∈ d.S, ∀ w ∈ d.W, g * w * g⁻¹ ∈ d.W := fun g hg w hw =>
    (mem_normalizer_iff.1 (d.S_le_normalizer_W hg) w).1 hw
  have hu : d.x₁ a ∈ d.S := d.U₁_le_S (d.x₁_mem_U₁ a)
  have hv : d.x₂ b ∈ d.S := d.D_le_S (d.x₂_mem_D b)
  have hz : d.x₃ c ∈ d.S := d.D_le_S (d.F_le_D (d.mem_F_iff.2 ⟨c, 1, one_mem _, mul_one _⟩))
  have hs₀ : d.x₁ a * (d.x₂ b * d.x₃ c) ∈ d.S := mul_mem hu (mul_mem hv hz)
  have hz_inv : (d.x₃ c)⁻¹ = d.x₃ c :=
    inv_eq_of_mul_eq_one_right (by rw [← d.x₃_add, CharTwo.add_self_eq_zero, d.x₃_zero])
  have hu_inv : (d.x₁ a)⁻¹ = d.x₁ a := d.x₁_inv a
  have hvz : d.x₂ b * d.x₃ c = d.x₃ c * d.x₂ b := (d.commute₂₃ b c).eq
  have e₀ : d.x₁ a * (d.x₂ b * d.x₃ c) * (d.x₁ a * (d.x₂ b * d.x₃ c)) =
      ⁅d.x₁ a, d.x₂ b⁆ * (d.x₂ b * ⁅d.x₁ a, d.x₃ c⁆ * d.x₂ b) := by
    calc d.x₁ a * (d.x₂ b * d.x₃ c) * (d.x₁ a * (d.x₂ b * d.x₃ c)) =
        d.x₁ a * d.x₂ b * d.x₃ c * d.x₁ a * (d.x₃ c * d.x₂ b) := by rw [← hvz]; group
      _ = d.x₁ a * d.x₂ b * d.x₃ c * (d.x₁ a)⁻¹ * (d.x₃ c)⁻¹ * d.x₂ b := by
          rw [hu_inv, hz_inv]; group
      _ = ⁅d.x₁ a, d.x₂ b⁆ * (d.x₂ b * ⁅d.x₁ a, d.x₃ c⁆ * d.x₂ b) := by
          simp only [commutatorElement_def]; group
  have hω : ⁅d.x₁ a, d.x₃ c⁆ ∈ d.W := by
    rw [d.comm₁₃]
    exact mul_mem (mul_mem (d.x₄_mem_W _) (d.x₅_mem_W _)) (d.x₆_mem_W _)
  have hω' : (d.x₃ (a * b))⁻¹ * ⁅d.x₁ a, d.x₂ b⁆ ∈ d.W := by
    rw [d.comm₁₂, mul_assoc, mul_assoc, inv_mul_cancel_left]
    exact mul_mem (d.x₄_mem_W _) (d.x₅_mem_W _)
  have hs₀sq : d.x₁ a * (d.x₂ b * d.x₃ c) * (d.x₁ a * (d.x₂ b * d.x₃ c)) ∈ d.W := by
    have e : d.x₁ a * (d.x₂ b * d.x₃ c) * (d.x₁ a * (d.x₂ b * d.x₃ c)) =
        (d.x₁ a * (d.x₂ b * (d.x₃ c * w₀)) * (d.x₁ a * (d.x₂ b * (d.x₃ c * w₀)))) *
          (w₀⁻¹ * ((d.x₁ a * (d.x₂ b * d.x₃ c))⁻¹ * w₀⁻¹ *
            (d.x₁ a * (d.x₂ b * d.x₃ c))⁻¹⁻¹)) := by group
    rw [e]
    exact mul_mem h (mul_mem (inv_mem hw₀) (hWN _ (inv_mem hs₀) _ (inv_mem hw₀)))
  have h3 : d.x₃ (a * b) ∈ d.W := by
    rw [e₀] at hs₀sq
    have hvω := hWN _ hv _ hω
    rw [d.x₂_inv] at hvω
    have h1 := mul_mem hs₀sq (inv_mem hvω)
    rw [mul_inv_cancel_right] at h1
    have h2 := mul_mem h1 (inv_mem hω')
    rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at h2
  rcases mul_eq_zero.1 (d.x₃_mem_W_iff.1 h3) with ha | hb
  · right
    rw [ha, d.x₁_zero, one_mul]
    exact hn
  · left
    have hb' : b = 0 := Subtype.ext hb
    rw [hb', d.x₂_zero, one_mul]
    exact d.mem_M_iff.2 ⟨a, _, hn', rfl⟩

theorem mul_self_mem_W_of_mem_D {s : X} (hs : s ∈ d.D) : s * s ∈ d.W := by
  obtain ⟨b, n', hn', rfl⟩ := d.mem_D_iff.1 hs
  obtain ⟨c, w₀, hw₀, rfl⟩ := d.mem_F_iff.1 hn'
  have hvz : d.x₂ b * d.x₃ c = d.x₃ c * d.x₂ b := (d.commute₂₃ b c).eq
  have hz2 : d.x₃ c * d.x₃ c = 1 := by
    rw [← d.x₃_add, CharTwo.add_self_eq_zero, d.x₃_zero]
  have hs₀ : d.x₂ b * d.x₃ c ∈ d.S :=
    d.D_le_S (mul_mem (d.x₂_mem_D b) (d.F_le_D (d.mem_F_iff.2 ⟨c, 1, one_mem _, mul_one _⟩)))
  have hs₀inv : (d.x₂ b * d.x₃ c)⁻¹ = d.x₂ b * d.x₃ c := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc d.x₂ b * d.x₃ c * (d.x₂ b * d.x₃ c) = d.x₂ b * (d.x₃ c * d.x₂ b) * d.x₃ c := by group
      _ = d.x₂ b * (d.x₂ b * d.x₃ c) * d.x₃ c := by rw [hvz]
      _ = (d.x₂ b * d.x₂ b) * (d.x₃ c * d.x₃ c) := by group
      _ = 1 := by rw [d.x₂_mul_self, hz2, one_mul]
  have hconj : (d.x₂ b * d.x₃ c)⁻¹ * w₀ * (d.x₂ b * d.x₃ c) ∈ d.W := by
    have := (mem_normalizer_iff.1 (d.S_le_normalizer_W (inv_mem hs₀)) w₀).1 hw₀
    rwa [inv_inv] at this
  have e : d.x₂ b * (d.x₃ c * w₀) * (d.x₂ b * (d.x₃ c * w₀)) =
      (d.x₂ b * d.x₃ c)⁻¹ * w₀ * (d.x₂ b * d.x₃ c) * w₀ := by
    rw [hs₀inv]
    group
  rw [e]
  exact mul_mem hconj hw₀

end TrialityD4Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem le_or_le_of_forall_mem_or_D3 {K : Type*} [Group K] {H A B : Subgroup K}
    (hH : ∀ y ∈ H, y ∈ A ∨ y ∈ B) : H ≤ A ∨ H ≤ B := by
  by_contra hne
  obtain ⟨hA, hB⟩ := not_or.1 hne
  obtain ⟨a, haH, haA⟩ := Set.not_subset.1 hA
  obtain ⟨b, hbH, hbB⟩ := Set.not_subset.1 hB
  have haB := (hH a haH).resolve_left haA
  have hbA := (hH b hbH).resolve_right hbB
  rcases hH (a * b) (mul_mem haH hbH) with hab | hab
  · apply haA
    have := mul_mem hab (inv_mem hbA)
    rwa [mul_inv_cancel_right] at this
  · apply hbB
    have := mul_mem (inv_mem haB) hab
    rwa [inv_mul_cancel_left] at this

namespace Setup

section Squares

theorem inv_mul_conj_mem_yamadaM₂_of (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {a x : G}
    (haN : a ∈ centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G))
    (haM₃ : a ∈ normalizer (yamadaM₃ d t : Set G))
    (haW : ∀ w ∈ d.W.map L.subtype, w⁻¹ * (a * w * a⁻¹) ∈ d.Y.map L.subtype)
    (hx : x ∈ yamadaM₃ d t) : x⁻¹ * (a * x * a⁻¹) ∈ yamadaM₂ d t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  obtain ⟨_, _, φ, hφ, hφeq⟩ :=
    h.yamada_5_17_1_module d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hxL : x ∈ yamadaL₃ d t := (Subgroup.mem_inf.1 hx).1
  obtain ⟨hw, ex⟩ := hφ ⟨x, hxL⟩
  obtain ⟨hax, haw, eax⟩ := hφeq a haN ⟨x, hxL⟩
  have key : φ (QuotientGroup.mk ⟨x, hxL⟩) = φ (QuotientGroup.mk ⟨a * x * a⁻¹, hax⟩) := by
    rw [ex, eax, QuotientGroup.eq, mem_subgroupOf]
    exact haW _ hw
  have h1 := QuotientGroup.eq.1 (φ.injective key)
  rw [mem_subgroupOf] at h1
  have h2 : x⁻¹ * (a * x * a⁻¹) ∈ centralizer (yamadaY₂ d t : Set G) :=
    mul_mem (inv_mem (Subgroup.mem_inf.1 hx).2)
      (Subgroup.mem_inf.1 ((mem_normalizer_iff.1 haM₃ x).1 hx)).2
  rw [h.yamadaM₂_eq_inf_centralizer d h591 h592]
  exact Subgroup.mem_inf.2 ⟨h1, h2⟩

theorem S_map_le_normalizer_yamadaW₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    d.S.map L.subtype ≤ normalizer (yamadaW₂ d t : Set G) ⊓ normalizer (yamadaW₃ d t : Set G) := by
  have h592 := h.yamada_5_9_2 d hlay
  intro s hs
  have hsY₂ : s ∈ normalizer (yamadaY₂ d t : Set G) :=
    yamadaR₂_le_normalizer_yamadaY₂ d h592 (h.yamada_5_10_1 d hlay)
      (h.yamada_5_10_2 d hlay) (mem_sup_right hs)
  have hsW₂ : s ∈ normalizer (yamadaW₂ d t : Set G) :=
    mem_normalizer_sup (map_le_normalizer_map d.S_le_normalizer_W hs) hsY₂
  exact Subgroup.mem_inf.2 ⟨hsW₂, mem_normalizer_inf_D4 (h.S_le_normalizer_yamadaL₃ d hs)
    (mem_normalizer_centralizer_D4 hsW₂)⟩

theorem coe_yamadaR₃_eq_mul (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    ((yamadaR₃ d t : Subgroup G) : Set G) =
      ((yamadaW₃ d t ⊔ zpowers t : Subgroup G) : Set G) *
        ((d.S.map L.subtype : Subgroup G) : Set G) := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have hR₃ := (h.yamada_5_17_2 d hNH (h.yamada_5_6_1 d hlay) (h.yamada_5_6_2 d hlay)
    (h.yamada_5_9_1 d hlay) (h.yamada_5_9_2 d hlay) (h.yamada_5_9_3 d hlay)
    (h.yamada_5_10_1 d hlay) (h.yamada_5_10_2 d hlay)).2
  have hSN : d.S.map L.subtype ≤ normalizer ((yamadaW₃ d t ⊔ zpowers t : Subgroup G) : Set G) :=
    fun s hs => mem_normalizer_sup (Subgroup.mem_inf.1 (h.S_map_le_normalizer_yamadaW₃ d hlay
      hs)).2 (mem_normalizer_zpowers_of_comm_D4
        (mem_centralizer_singleton_iff.1 (h.L_le_centralizer (map_subtype_le _ hs))))
  rw [← coe_mul_of_right_le_normalizer_left _ _ hSN]
  congr 1
  have hW₂W₃ : yamadaW₂ d t ≤ yamadaW₃ d t := by
    rw [← h.yamadaM₂_inf_yamadaW₃ d hlay]
    exact inf_le_right
  have hW₃L₃ : yamadaW₃ d t ≤ yamadaL₃ d t := inf_le_left
  have htL₃ : t ∈ yamadaL₃ d t := by
    rw [h.yamadaL₃_eq_sup d hlay]
    exact mem_sup_right (mem_zpowers t)
  refine le_antisymm ?_ (sup_le (sup_le (hW₃L₃.trans (hR₃ ▸ le_sup_left))
    ((zpowers_le).2 (hR₃ ▸ mem_sup_left htL₃ : t ∈ yamadaR₃ d t))) (hR₃ ▸ le_sup_right))
  rw [hR₃, h.yamadaL₃_eq_sup d hlay, ← h.yamadaM₂_sup_yamadaW₃ d hlay]
  refine sup_le (sup_le (sup_le ?_ (le_sup_left.trans le_sup_left)) (le_sup_right.trans
    le_sup_left)) le_sup_right
  exact sup_le ((map_mono d.M_le_S).trans le_sup_right)
    ((le_sup_right.trans hW₂W₃).trans (le_sup_left.trans le_sup_left))

theorem sup_zpowers_le_yamadaL₃_inf_yamadaC₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaW₃ d t ⊔ zpowers t ≤ yamadaL₃ d t ⊓ yamadaC₅ d t := by
  have htL₃ : t ∈ yamadaL₃ d t := by
    rw [h.yamadaL₃_eq_sup d hlay]
    exact mem_sup_right (mem_zpowers t)
  exact le_inf (sup_le inf_le_left ((zpowers_le).2 htL₃))
    (sup_le (h.yamadaW₃_le_yamadaC₅ d hlay) ((zpowers_le).2 (h.t_mem_yamadaC₅ d)))

theorem exists_mul_eq_of_mem_yamadaR₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G}
    (hx : x ∈ yamadaR₃ d t) : ∃ z ∈ yamadaW₃ d t ⊔ zpowers t, ∃ s ∈ d.S,
      z * ((s : L) : G) = x ∧ (x * x ∈ yamadaW₂ d t ↔ s * s ∈ d.W) := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have hW₂N : yamadaL₃ d t ≤ normalizer (yamadaW₂ d t : Set G) := fun g hg =>
    (h.normalizer_yamadaV₂_le d h562 h592).1 (h.yamadaL₃_le_normalizer_yamadaV₂ d hNH
      (h.yamada_5_6_1 d hlay) h562 (h.yamada_5_9_1 d hlay) h592 (h.yamada_5_9_3 d hlay)
      (h.yamada_5_10_1 d hlay) (h.yamada_5_10_2 d hlay) hg)
  have htL₃ : t ∈ yamadaL₃ d t := by
    rw [h.yamadaL₃_eq_sup d hlay]
    exact mem_sup_right (mem_zpowers t)
  have hx' : x ∈ ((yamadaR₃ d t : Subgroup G) : Set G) := hx
  rw [h.coe_yamadaR₃_eq_mul d hlay] at hx'
  obtain ⟨z, hz, _, ⟨s, hs, rfl⟩, e⟩ := hx'
  replace hz : z ∈ yamadaW₃ d t ⊔ zpowers t := hz
  replace hs : s ∈ d.S := hs
  replace e : z * ((s : L) : G) = x := e
  have hzL₃ := (Subgroup.mem_inf.1 (h.sup_zpowers_le_yamadaL₃_inf_yamadaC₅ d hlay hz)).1
  have hsS : ((s : L) : G) ∈ d.S.map L.subtype := ⟨s, hs, rfl⟩
  have hsW₃ := (Subgroup.mem_inf.1 (h.S_map_le_normalizer_yamadaW₃ d hlay hsS)).2
  have hsN : ((s : L) : G) ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) :=
    Subgroup.mem_inf.2 ⟨h.L_le_centralizer s.2, map_le_normalizer_map d.S_le_normalizer_Y hsS⟩
  have hsM₃ : ((s : L) : G) ∈ normalizer (yamadaM₃ d t : Set G) :=
    mem_normalizer_inf_D4 (h.S_le_normalizer_yamadaL₃ d hsS) (mem_normalizer_centralizer_D4
      (yamadaR₂_le_normalizer_yamadaY₂ d h592 (h.yamada_5_10_1 d hlay)
        (h.yamada_5_10_2 d hlay) (mem_sup_right hsS)))
  have hsW : ∀ w ∈ d.W.map L.subtype,
      w⁻¹ * (((s : L) : G) * w * ((s : L) : G)⁻¹) ∈ d.Y.map L.subtype := by
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨w⁻¹ * (s * w * s⁻¹), ?_, by simp⟩
    have := inv_mem (d.commutator_S_W (commutator_mem_commutator hs (inv_mem hw)))
    rwa [commutatorElement_def, show (s * w⁻¹ * s⁻¹ * w⁻¹⁻¹)⁻¹ = w⁻¹ * (s * w * s⁻¹) by group]
      at this
  have hcom : ∀ w ∈ yamadaW₃ d t, ((s : L) : G) * w * ((s : L) : G)⁻¹ * w⁻¹ ∈ yamadaW₂ d t :=
    fun w hw => by
      have h1 := h.inv_mul_conj_mem_yamadaM₂_of d hlay hsN hsM₃ hsW
        (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hw).1, centralizer_le
          (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) (Subgroup.mem_inf.1 hw).2⟩)
      have h2 : w⁻¹ * (((s : L) : G) * w * ((s : L) : G)⁻¹) ∈ yamadaW₃ d t :=
        mul_mem (inv_mem hw) ((mem_normalizer_iff.1 hsW₃ w).1 hw)
      have h3 : w⁻¹ * (((s : L) : G) * w * ((s : L) : G)⁻¹) ∈ yamadaW₂ d t := by
        rw [← h.yamadaM₂_inf_yamadaW₃ d hlay]
        exact Subgroup.mem_inf.2 ⟨h1, h2⟩
      have h4 := (mem_normalizer_iff.1 (hW₂N (Subgroup.mem_inf.1 hw).1) _).1 h3
      rwa [show w * (w⁻¹ * (((s : L) : G) * w * ((s : L) : G)⁻¹)) * w⁻¹ =
        ((s : L) : G) * w * ((s : L) : G)⁻¹ * w⁻¹ by group] at h4
  have htW₃ : t ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaL₃_le_normalizer_yamadaW₃ d hlay htL₃
  have hst : ((s : L) : G) * t = t * ((s : L) : G) :=
    mem_centralizer_singleton_iff.1 (h.L_le_centralizer s.2)
  have hc : ((s : L) : G) * z * ((s : L) : G)⁻¹ * z⁻¹ ∈ yamadaW₂ d t := by
    have hz' := hz
    rw [h.mem_sup_zpowers_iff_of_normalizer htW₃] at hz'
    rcases hz' with hz' | hz'
    · exact hcom z hz'
    · have h1 := (mem_normalizer_iff.1 (hW₂N htL₃) _).1 (hcom _ hz')
      have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
      have e1 : ((s : L) : G) * z * ((s : L) : G)⁻¹ * z⁻¹ =
          t * (((s : L) : G) * (t * z) * ((s : L) : G)⁻¹ * (t * z)⁻¹) * t⁻¹ := by
        calc ((s : L) : G) * z * ((s : L) : G)⁻¹ * z⁻¹ =
            ((s : L) : G) * (t * (t * z)) * ((s : L) : G)⁻¹ * (t * (t * z))⁻¹ := by
              rw [← mul_assoc t t z, h.t_mul_t, one_mul]
          _ = (((s : L) : G) * t) * (t * z) * ((s : L) : G)⁻¹ * (t * z)⁻¹ * t⁻¹ := by group
          _ = t * (((s : L) : G) * (t * z) * ((s : L) : G)⁻¹ * (t * z)⁻¹) * t⁻¹ := by
              rw [hst]; group
      rw [e1]
      exact h1
  have hP : z * (((s : L) : G) * z * ((s : L) : G)⁻¹ * z⁻¹) * z⁻¹ * (z * z) ∈ yamadaW₂ d t :=
    mul_mem ((mem_normalizer_iff.1 (hW₂N hzL₃) _).1 hc)
      (h.mul_self_mem_yamadaW₂_of_mem_yamadaL₃ d hlay hzL₃)
  have hxx : x * x = (z * (((s : L) : G) * z * ((s : L) : G)⁻¹ * z⁻¹) * z⁻¹ * (z * z)) *
      (((s : L) : G) * ((s : L) : G)) := by
    rw [← e]
    group
  have hsL : (((s * s : L) : G) ∈ yamadaW₂ d t) ↔ s * s ∈ d.W := by
    constructor
    · intro h1
      have h2 : ((s * s : L) : G) ∈ yamadaW₂ d t ⊓ centralizer ({t} : Set G) :=
        Subgroup.mem_inf.2 ⟨h1, h.L_le_centralizer (s * s).2⟩
      rw [h.yamadaW₂_inf_centralizer d h592] at h2
      obtain ⟨w, hw, hwe⟩ := h2
      rwa [← Subtype.ext hwe]
    · intro h1
      exact mem_sup_left ⟨s * s, h1, rfl⟩
  refine ⟨z, hz, s, hs, e, ?_⟩
  rw [← hsL, hxx]
  constructor
  · intro h1
    have := mul_mem (inv_mem hP) h1
    rwa [inv_mul_cancel_left] at this
  · intro h1
    exact mul_mem hP h1

theorem mem_yamadaL₃_or_mem_of_mul_self_mem (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G}
    (hx : x ∈ yamadaR₃ d t) (hxx : x * x ∈ yamadaW₂ d t) :
    x ∈ yamadaL₃ d t ∨ x ∈ yamadaR₃ d t ⊓ yamadaC₅ d t := by
  have hL₂L₃ := h.yamadaL₂_le_yamadaL₃ d (h.normalizerHyp_of_layerHyp d hlay) (h.yamada_5_6_1 d
    hlay)
    (h.yamada_5_6_2 d hlay) (h.yamada_5_9_1 d hlay) (h.yamada_5_9_2 d hlay)
    (h.yamada_5_9_3 d hlay) (h.yamada_5_10_1 d hlay) (h.yamada_5_10_2 d hlay)
  obtain ⟨z, hz, s, hs, e, hiff⟩ := h.exists_mul_eq_of_mem_yamadaR₃ d hlay hx
  have hzLC := Subgroup.mem_inf.1 (h.sup_zpowers_le_yamadaL₃_inf_yamadaC₅ d hlay hz)
  rcases d.mem_M_or_mem_D_of_mul_self_mem_W hs (hiff.1 hxx) with hsM | hsD
  · left
    rw [← e]
    exact mul_mem hzLC.1 ((le_sup_left.trans (h.tM_le_yamadaL₂ d)).trans hL₂L₃ ⟨s, hsM, rfl⟩)
  · right
    refine Subgroup.mem_inf.2 ⟨hx, ?_⟩
    rw [← e]
    exact mul_mem hzLC.2 ((h.D_map_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t)
      ⟨s, hsD, rfl⟩)

theorem mul_self_mem_yamadaW₂_of_mem_inf (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G}
    (hx : x ∈ yamadaR₃ d t ⊓ yamadaC₅ d t) : x * x ∈ yamadaW₂ d t := by
  obtain ⟨z, hz, s, hs, e, hiff⟩ :=
    h.exists_mul_eq_of_mem_yamadaR₃ d hlay (Subgroup.mem_inf.1 hx).1
  refine hiff.2 (d.mul_self_mem_W_of_mem_D ?_)
  have hsC : ((s : L) : G) ∈ yamadaC₅ d t ⊓ d.S.map L.subtype := by
    refine Subgroup.mem_inf.2 ⟨?_, ⟨s, hs, rfl⟩⟩
    have := mul_mem (inv_mem (Subgroup.mem_inf.1
      (h.sup_zpowers_le_yamadaL₃_inf_yamadaC₅ d hlay hz)).2) (Subgroup.mem_inf.1 hx).2
    rwa [← e, inv_mul_cancel_left] at this
  rw [h.yamadaC₅_inf_S_map d hlay] at hsC
  obtain ⟨s', hs', hse⟩ := hsC
  rwa [← Subtype.ext hse]

end Squares

section Char

theorem yamadaF₂_le_yamadaR₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaF₂ d t ≤ yamadaR₃ d t := by
  rw [← h.commutator_yamadaR₃ d hlay]
  exact commutator_le.2 fun a ha b hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem automorphism_mem_yamadaF₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (ϕ : yamadaR₃ d t ≃* yamadaR₃ d t) {x : yamadaR₃ d t} (hx : (x : G) ∈ yamadaF₂ d t) :
    ((ϕ x : yamadaR₃ d t) : G) ∈ yamadaF₂ d t := by
  have hmap : (⁅(⊤ : Subgroup (yamadaR₃ d t)), ⊤⁆ : Subgroup (yamadaR₃ d t)).map
      (yamadaR₃ d t).subtype = ⁅yamadaR₃ d t, yamadaR₃ d t⁆ := by
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  have hϕ : (⁅(⊤ : Subgroup (yamadaR₃ d t)), ⊤⁆ : Subgroup (yamadaR₃ d t)).map
      ϕ.toMonoidHom = ⁅(⊤ : Subgroup (yamadaR₃ d t)), ⊤⁆ := by
    rw [map_commutator, map_top_of_surjective _ ϕ.surjective]
  rw [← h.commutator_yamadaR₃ d hlay, ← hmap] at hx ⊢
  obtain ⟨y, hy, hyx⟩ := hx
  obtain rfl : y = x := Subtype.ext hyx
  refine ⟨ϕ y, ?_, rfl⟩
  rw [← hϕ]
  exact ⟨y, hy, rfl⟩

theorem automorphism_mem_yamadaY₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (ϕ : yamadaR₃ d t ≃* yamadaR₃ d t) {x : yamadaR₃ d t} (hx : (x : G) ∈ yamadaY₂ d t) :
    ((ϕ x : yamadaR₃ d t) : G) ∈ yamadaY₂ d t := by
  have hZ := yamadaF₂_inf_centralizer d (h.yamada_5_9_2 d hlay)
  rw [← hZ] at hx ⊢
  obtain ⟨hxF, hxC⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨h.automorphism_mem_yamadaF₂ d hlay ϕ hxF,
    mem_centralizer_iff.2 fun z hz => ?_⟩
  have hzR := h.yamadaF₂_le_yamadaR₃ d hlay hz
  set y := ϕ.symm ⟨z, hzR⟩ with hy
  have hyF : (y : G) ∈ yamadaF₂ d t := h.automorphism_mem_yamadaF₂ d hlay ϕ.symm hz
  have hxy : y * x = x * y := Subtype.ext (mem_centralizer_iff.1 hxC _ hyF)
  have := congrArg (fun r => ((ϕ r : yamadaR₃ d t) : G)) hxy
  simp only [map_mul, hy, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at this
  exact this

theorem mem_yamadaW₂_iff (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} :
    x ∈ yamadaW₂ d t ↔ x ∈ yamadaF₂ d t ∧
      ∀ r ∈ yamadaR₃ d t, x * r * x⁻¹ * r⁻¹ ∈ yamadaY₂ d t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have hR₃ := (h.yamada_5_17_2 d hNH h561 h562 h591 h592 h593 h5101 h5102).2
  have hSR₃ : d.S.map L.subtype ≤ yamadaR₃ d t := hR₃ ▸ le_sup_right
  have hFY₂ : d.F.map L.subtype ≤ normalizer (yamadaY₂ d t : Set G) :=
    (map_mono d.F_le_M).trans (M_le_normalizer_yamadaY₂ d h592)
  constructor
  · intro hx
    refine ⟨sup_le_sup_right (map_mono d.W_le_F) _ hx, fun r hr => ?_⟩
    have hrE := ((h.mem_centralizerW₂Y₂_iff d hNH h561 h562 h591 h592 h593 h5101 h5102).1
      (h.yamadaR₃_le_centralizerW₂Y₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hr)).2
    have h1 := hrE _ (inv_mem hx)
    rw [inv_inv] at h1
    have hk : x * (r * x⁻¹ * r⁻¹ * x) * x⁻¹ = r * x⁻¹ * r⁻¹ * x := by
      rw [yamadaW₂_mul_comm d h592 hx (mem_sup_right h1), mul_inv_cancel_right]
    rw [show x * r * x⁻¹ * r⁻¹ = x * (r * x⁻¹ * r⁻¹ * x) * x⁻¹ by group, hk]
    exact h1
  · rintro ⟨hxF, hxr⟩
    have hx' : x ∈ ((d.F.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) : Set G) := hxF
    rw [coe_mul_of_left_le_normalizer_right _ _ hFY₂] at hx'
    obtain ⟨_, ⟨a, ha, rfl⟩, y, hy, e⟩ := hx'
    simp only [Subgroup.coe_subtype] at e
    have haW : a ∈ d.W := d.mem_W_iff_forall.2 ⟨d.F_le_S ha, fun s hs => by
      have hsR : ((s : L) : G) ∈ yamadaR₃ d t := hSR₃ ⟨s, hs, rfl⟩
      have hsY₂ : ((s : L) : G) ∈ normalizer (yamadaY₂ d t : Set G) :=
        yamadaR₂_le_normalizer_yamadaY₂ d h592 h5101 h5102 (mem_sup_right ⟨s, hs, rfl⟩)
      have h1 := hxr _ hsR
      rw [← e] at h1
      have hys : y * ((s : L) : G) * y⁻¹ * ((s : L) : G)⁻¹ ∈ yamadaY₂ d t := by
        have := mul_mem hy ((mem_normalizer_iff.1 hsY₂ _).1 (inv_mem hy))
        rwa [← mul_assoc, ← mul_assoc] at this
      have hays : ((a : L) : G) * (y * ((s : L) : G) * y⁻¹ * ((s : L) : G)⁻¹) *
          ((a : L) : G)⁻¹ ∈ yamadaY₂ d t :=
        (mem_normalizer_iff.1 (hFY₂ ⟨a, ha, rfl⟩) _).1 hys
      have h2 : ((a : L) : G) * ((s : L) : G) * ((a : L) : G)⁻¹ * ((s : L) : G)⁻¹ ∈
          yamadaY₂ d t := by
        have e2 : ((a : L) : G) * ((s : L) : G) * ((a : L) : G)⁻¹ * ((s : L) : G)⁻¹ =
            (((a : L) : G) * (y * ((s : L) : G) * y⁻¹ * ((s : L) : G)⁻¹) *
              ((a : L) : G)⁻¹)⁻¹ * (((a : L) : G) * y * ((s : L) : G) *
                (((a : L) : G) * y)⁻¹ * ((s : L) : G)⁻¹) := by group
        rw [e2]
        exact mul_mem (inv_mem hays) h1
      have h3 : ((⁅a, s⁆ : L) : G) ∈ yamadaY₂ d t ⊓ centralizer ({t} : Set G) := by
        refine Subgroup.mem_inf.2 ⟨?_, h.L_le_centralizer (⁅a, s⁆ : L).2⟩
        rw [commutatorElement_def]
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h2
      rw [h592.2.2.2.2] at h3
      obtain ⟨k, hk, hke⟩ := h3
      rwa [← Subtype.ext hke]⟩
    rw [← e]
    exact mul_mem (mem_sup_left ⟨a, haW, rfl⟩) (mem_sup_right hy)

theorem automorphism_mem_yamadaW₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (ϕ : yamadaR₃ d t ≃* yamadaR₃ d t) {x : yamadaR₃ d t} (hx : (x : G) ∈ yamadaW₂ d t) :
    ((ϕ x : yamadaR₃ d t) : G) ∈ yamadaW₂ d t := by
  rw [h.mem_yamadaW₂_iff d hlay] at hx ⊢
  refine ⟨h.automorphism_mem_yamadaF₂ d hlay ϕ hx.1, fun r hr => ?_⟩
  set r' := ϕ.symm ⟨r, hr⟩ with hr'
  have h1 : ((x * r' * x⁻¹ * r'⁻¹ : yamadaR₃ d t) : G) ∈ yamadaY₂ d t := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hx.2 _ r'.2
  have h2 := h.automorphism_mem_yamadaY₂ d hlay ϕ h1
  simpa only [map_mul, map_inv, hr', MulEquiv.apply_symm_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] using h2

theorem x₂_one_not_mem_yamadaL₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    ((d.x₂ 1 : L) : G) ∉ yamadaL₃ d t := fun hx => by
  have h1 := mem_centralizer_iff.1 (h.yamadaL₃_le_centralizer_Y d (h.yamada_5_9_2 d hlay)
    (h.yamada_5_20 d hlay) hx) _ ⟨d.x₅ 1, d.x₅_mem_Y 1, rfl⟩
  have h2 : d.x₅ 1 * d.x₂ 1 = d.x₂ 1 * d.x₅ 1 := Subtype.ext h1
  have h3 := d.comm₂₅ 1 1
  rw [commutatorElement_eq_one_iff_mul_comm.2 h2.symm, mul_one] at h3
  exact one_ne_zero (d.x₆_injective (h3.symm.trans d.x₆_zero.symm))

theorem automorphism_mem_yamadaL₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (ϕ : yamadaR₃ d t ≃* yamadaR₃ d t) {x : yamadaR₃ d t} (hx : (x : G) ∈ yamadaL₃ d t) :
    ((ϕ x : yamadaR₃ d t) : G) ∈ yamadaL₃ d t := by
  have hL₃R₃ := h.yamadaL₃_le_yamadaR₃_D3 d hlay
  have hTR₃ : yamadaR₃ d t ⊓ yamadaC₅ d t ≤ yamadaR₃ d t := inf_le_left
  have hH : ∀ y ∈ ((yamadaL₃ d t).subgroupOf (yamadaR₃ d t)).map ϕ.toMonoidHom,
      y ∈ (yamadaL₃ d t).subgroupOf (yamadaR₃ d t) ∨
        y ∈ (yamadaR₃ d t ⊓ yamadaC₅ d t).subgroupOf (yamadaR₃ d t) := by
    rintro _ ⟨z, hz, rfl⟩
    replace hz := mem_subgroupOf.1 hz
    rw [mem_subgroupOf, mem_subgroupOf]
    have hzz : ((z * z : yamadaR₃ d t) : G) ∈ yamadaW₂ d t :=
      h.mul_self_mem_yamadaW₂_of_mem_yamadaL₃ d hlay hz
    have h1 := h.automorphism_mem_yamadaW₂ d hlay ϕ hzz
    rw [map_mul, Subgroup.coe_mul] at h1
    exact h.mem_yamadaL₃_or_mem_of_mul_self_mem d hlay (ϕ z).2 h1
  rcases le_or_le_of_forall_mem_or_D3 hH with hle | hle
  · exact mem_subgroupOf.1 (hle ⟨x, mem_subgroupOf.2 hx, rfl⟩)
  · exfalso
    have hc1 : Nat.card (((yamadaL₃ d t).subgroupOf (yamadaR₃ d t)).map ϕ.toMonoidHom) =
        2 * (2 ^ f) ^ 16 := by
      rw [Subgroup.card_map_of_injective ϕ.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₃R₃).toEquiv, h.card_yamadaL₃ d hlay]
    have hc2 := Subgroup.card_le_of_le hle
    rw [hc1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTR₃).toEquiv,
      h.card_yamadaR₃_inf_yamadaC₅ d hlay] at hc2
    have hlt : (2 ^ f) ^ 14 < (2 ^ f) ^ 16 :=
      Nat.pow_lt_pow_right (by have := d.two_le_q; omega) (by norm_num)
    exact absurd hc2 (not_le.2 (Nat.mul_lt_mul_of_pos_left hlt (by norm_num)))

theorem automorphism_mem_yamadaC₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (ϕ : yamadaR₃ d t ≃* yamadaR₃ d t) {x : yamadaR₃ d t} (hx : (x : G) ∈ yamadaC₅ d t) :
    ((ϕ x : yamadaR₃ d t) : G) ∈ yamadaC₅ d t := by
  have hH : ∀ y ∈ ((yamadaR₃ d t ⊓ yamadaC₅ d t).subgroupOf (yamadaR₃ d t)).map ϕ.toMonoidHom,
      y ∈ (yamadaL₃ d t).subgroupOf (yamadaR₃ d t) ∨
        y ∈ (yamadaR₃ d t ⊓ yamadaC₅ d t).subgroupOf (yamadaR₃ d t) := by
    rintro _ ⟨z, hz, rfl⟩
    replace hz := mem_subgroupOf.1 hz
    rw [mem_subgroupOf, mem_subgroupOf]
    have hzz : ((z * z : yamadaR₃ d t) : G) ∈ yamadaW₂ d t :=
      h.mul_self_mem_yamadaW₂_of_mem_inf d hlay hz
    have h1 := h.automorphism_mem_yamadaW₂ d hlay ϕ hzz
    rw [map_mul, Subgroup.coe_mul] at h1
    exact h.mem_yamadaL₃_or_mem_of_mul_self_mem d hlay (ϕ z).2 h1
  rcases le_or_le_of_forall_mem_or_D3 hH with hle | hle
  · exfalso
    have hNH := h.normalizerHyp_of_layerHyp d hlay
    have hR₃ := (h.yamada_5_17_2 d hNH (h.yamada_5_6_1 d hlay) (h.yamada_5_6_2 d hlay)
      (h.yamada_5_9_1 d hlay) (h.yamada_5_9_2 d hlay) (h.yamada_5_9_3 d hlay)
      (h.yamada_5_10_1 d hlay) (h.yamada_5_10_2 d hlay)).2
    have hx₂R : ((d.x₂ 1 : L) : G) ∈ yamadaR₃ d t :=
      (hR₃ ▸ le_sup_right : d.S.map L.subtype ≤ yamadaR₃ d t) ⟨_, d.D_le_S (d.x₂_mem_D 1), rfl⟩
    have hx₂T : ((d.x₂ 1 : L) : G) ∈ yamadaR₃ d t ⊓ yamadaC₅ d t :=
      Subgroup.mem_inf.2 ⟨hx₂R, (h.D_map_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t)
        ⟨_, d.x₂_mem_D 1, rfl⟩⟩
    have h1 : ((ϕ ⟨_, hx₂R⟩ : yamadaR₃ d t) : G) ∈ yamadaL₃ d t :=
      mem_subgroupOf.1 (hle ⟨⟨_, hx₂R⟩, mem_subgroupOf.2 hx₂T, rfl⟩)
    have h2 := h.automorphism_mem_yamadaL₃ d hlay ϕ.symm h1
    rw [MulEquiv.symm_apply_apply] at h2
    exact h.x₂_one_not_mem_yamadaL₃ d hlay h2
  · exact (Subgroup.mem_inf.1 (mem_subgroupOf.1
      (hle ⟨x, mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨x.2, hx⟩), rfl⟩))).2

theorem yamada_5_22_1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    ((yamadaF₃ d t ⊔ zpowers t).subgroupOf (yamadaR₃ d t)).Characteristic ∧
      ((yamadaL₃ d t).subgroupOf (yamadaR₃ d t)).Characteristic ∧
      ⁅yamadaR₃ d t, yamadaR₃ d t⁆ = yamadaF₂ d t := by
  refine ⟨characteristic_iff_map_le.2 fun ϕ => ?_, characteristic_iff_map_le.2 fun ϕ => ?_,
    h.commutator_yamadaR₃ d hlay⟩
  · rintro _ ⟨x, hx, rfl⟩
    replace hx := mem_subgroupOf.1 hx
    rw [mem_subgroupOf]
    rw [← h.yamadaL₃_inf_yamadaC₅ d hlay] at hx ⊢
    obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_inf.2 ⟨h.automorphism_mem_yamadaL₃ d hlay ϕ hxL,
      h.automorphism_mem_yamadaC₅ d hlay ϕ hxC⟩
  · rintro _ ⟨x, hx, rfl⟩
    replace hx := mem_subgroupOf.1 hx
    rw [mem_subgroupOf]
    exact h.automorphism_mem_yamadaL₃ d hlay ϕ hx

end Char

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
