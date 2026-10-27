module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL3Two
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LeviLongThree
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL3

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open scoped commutatorElement Pointwise

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem mem_D_of_commutatorElement_mem_V {s : X} (hs : s ∈ d.S)
    (h : ∀ w ∈ d.W, s * w * s⁻¹ * w⁻¹ ∈ d.V) : s ∈ d.D := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff.1 hs
  suffices ha : a = 0 by
    rw [ha, d.x₁_zero, one_mul]
    exact hn
  apply d.eq_zero_of_forall_tr_mul
  intro c
  have hx₄D : d.x₄ c ∈ d.D := (d.W_le_F.trans d.F_le_D) (d.x₄_mem_W c)
  obtain ⟨v, hv, hvn⟩ : ∃ v ∈ d.V, n * d.x₄ c * n⁻¹ = v * d.x₄ c :=
    ⟨n * d.x₄ c * n⁻¹ * (d.x₄ c)⁻¹, d.commutatorElement_mem_V_of_mem_D hn hx₄D, by group⟩
  have hvc : v * d.x₁ a = d.x₁ a * v :=
    mem_centralizer_iff.1 (d.S_le_centralizer_V (d.U₁_le_S (d.x₁_mem_U₁ a))) v hv
  have e : d.x₁ a * n * d.x₄ c * (d.x₁ a * n)⁻¹ * (d.x₄ c)⁻¹ = v * ⁅d.x₁ a, d.x₄ c⁆ := by
    rw [commutatorElement_def]
    calc d.x₁ a * n * d.x₄ c * (d.x₁ a * n)⁻¹ * (d.x₄ c)⁻¹ =
        d.x₁ a * (n * d.x₄ c * n⁻¹) * (d.x₁ a)⁻¹ * (d.x₄ c)⁻¹ := by group
      _ = (d.x₁ a * v) * d.x₄ c * (d.x₁ a)⁻¹ * (d.x₄ c)⁻¹ := by rw [hvn]; group
      _ = v * (d.x₁ a * d.x₄ c * (d.x₁ a)⁻¹ * (d.x₄ c)⁻¹) := by rw [← hvc]; group
  have h1 := h _ (d.x₄_mem_W c)
  rw [e, d.comm₁₄] at h1
  have h2 := mul_mem (inv_mem hv) h1
  rw [inv_mul_cancel_left] at h2
  exact d.x₅_mem_V_iff.1 h2

theorem mem_W_of_mem_M_of_commute {m : X} (hm : m ∈ d.M) (h : ∀ w ∈ d.W, m * w = w * m) :
    m ∈ d.W := by
  have hmD : m ∈ d.D := d.mem_D_of_commutatorElement_mem_V (d.M_le_S hm) fun w hw => by
    rw [h w hw, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  obtain ⟨b, n, hn, rfl⟩ := d.mem_F_iff.1 (d.M_inf_D_le_F ⟨hm, hmD⟩)
  suffices hb : b = 0 by
    rw [hb, d.x₃_zero, one_mul]
    exact hn
  apply d.eq_zero_of_forall_tr_mul
  intro c
  have h1 := h _ (d.x₄_mem_W c)
  have hn4 : n * d.x₄ c = d.x₄ c * n := d.mul_comm_of_mem_W hn (d.x₄_mem_W c)
  have h2 : d.x₃ b * d.x₄ c = d.x₄ c * d.x₃ b := by
    apply mul_right_cancel (b := n)
    calc d.x₃ b * d.x₄ c * n = d.x₃ b * (n * d.x₄ c) := by rw [mul_assoc, hn4]
      _ = d.x₃ b * n * d.x₄ c := by group
      _ = d.x₄ c * (d.x₃ b * n) := h1
      _ = d.x₄ c * d.x₃ b * n := by group
  have h3 := d.comm₃₄ b c
  rw [commutatorElement_eq_one_iff_mul_comm.2 h2] at h3
  exact d.x₆_injective (h3.symm.trans d.x₆_zero.symm)

theorem eq_zero_of_x₅_mem_U₄ {e : d.Γ₀} (he : d.x₅ e ∈ d.U₄) : e = 0 := by
  obtain ⟨c, hc⟩ := he
  have hc0 : c = 0 := d.x₄_mem_Y_iff.1 (hc ▸ d.x₅_mem_Y e)
  rw [hc0, d.x₄_zero] at hc
  exact d.x₅_injective (hc.symm.trans d.x₅_zero.symm)

end TrialityD4Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

section Card

theorem yamadaL₃_le_yamadaR₃_D3 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaL₃ d t ≤ yamadaR₃ d t := by
  rw [(h.yamada_5_17_2 d (h.normalizerHyp_of_layerHyp d hlay) (h.yamada_5_6_1 d hlay)
    (h.yamada_5_6_2 d hlay) (h.yamada_5_9_1 d hlay) (h.yamada_5_9_2 d hlay)
    (h.yamada_5_9_3 d hlay) (h.yamada_5_10_1 d hlay) (h.yamada_5_10_2 d hlay)).2]
  exact le_sup_left

theorem yamadaM₂_le_yamadaM₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaM₂ d t ≤ yamadaM₃ d t := by
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  rw [h.yamadaM₂_eq_inf_centralizer d h591 h592]
  exact inf_le_inf_right _ (h.yamadaL₂_le_yamadaL₃ d (h.normalizerHyp_of_layerHyp d hlay)
    (h.yamada_5_6_1 d hlay) (h.yamada_5_6_2 d hlay) h591 h592 (h.yamada_5_9_3 d hlay)
    (h.yamada_5_10_1 d hlay) (h.yamada_5_10_2 d hlay))

theorem card_yamadaL₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    Nat.card (yamadaL₃ d t) = 2 * (2 ^ f) ^ 16 := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have hL₂L₃ := h.yamadaL₂_le_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101 h5102
  obtain ⟨_, _, φ, -, -⟩ := h.yamada_5_17_1_module d hNH h561 h562 h591 h592 h593 h5101 h5102
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((yamadaL₂ d t).subgroupOf (yamadaL₃ d t))
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((d.Y.map L.subtype).subgroupOf (d.W.map L.subtype))
  rw [Nat.card_congr φ.toEquiv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₂L₃).toEquiv,
    (h.card_yamadaL₂_and d).1] at h1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (map_mono d.Y_le_W)).toEquiv,
    Subgroup.card_subtype, Subgroup.card_subtype, d.card_W, d.card_Y] at h2
  have hQ : Nat.card (d.W.map L.subtype ⧸ (d.Y.map L.subtype).subgroupOf (d.W.map L.subtype)) =
      (2 ^ f) ^ 3 := by
    refine Nat.eq_of_mul_eq_mul_right (m := (2 ^ f) ^ 2) (by positivity) ?_
    rw [← h2]
    ring
  rw [h1, hQ]
  ring

theorem card_yamadaM₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    Nat.card (yamadaM₃ d t) = (2 ^ f) ^ 16 := by
  have htL₃ : t ∈ yamadaL₃ d t := by
    rw [h.yamadaL₃_eq_sup d hlay]
    exact mem_sup_right (mem_zpowers t)
  have htM₃ : t ∈ normalizer (yamadaM₃ d t : Set G) :=
    mem_normalizer_inf_D4 (le_normalizer htL₃)
      (mem_normalizer_centralizer_D4 (h.t_mem_normalizer_yamadaY₂_D1 d))
  have h1 := h.card_sup_zpowers_of_not_mem htM₃ (h.t_not_mem_yamadaM₃ d hlay)
  rw [← h.yamadaL₃_eq_sup d hlay, h.card_yamadaL₃ d hlay] at h1
  exact (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h1).symm

end Card

section Three

omit [Finite G] in
theorem leviLong_map_le_centralizer_U₄ {q : ℕ} (d : TrialityD4Data L q) :
    d.leviLong.map L.subtype ≤ centralizer ((d.U₄.map L.subtype : Subgroup G) : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  refine mem_centralizer_iff.2 ?_
  rintro _ ⟨u, hu, rfl⟩
  exact congrArg Subtype.val (mem_centralizer_iff.1 (d.leviLong_le_centralizer_U₄ hl) u hu)

theorem leviLong_map_le_normalizer_yamadaM₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    d.leviLong.map L.subtype ≤ normalizer (yamadaM₂ d t : Set G) := by
  rw [h.yamadaM₂_eq_inf_centralizer d (h.yamada_5_9_1 d hlay) (h.yamada_5_9_2 d hlay)]
  rintro _ ⟨l, hl, rfl⟩
  exact mem_normalizer_inf_D4 (le_normalizer_yamadaL₂ d t (h.centralizer_inf_normalizer_Y_le d
    (Subgroup.mem_inf.2 ⟨h.L_le_centralizer l.2, coe_mem_normalizer_map
      (d.leviLong_le_normalizer_Y hl)⟩)))
    (mem_normalizer_centralizer_D4 (h.leviLong_map_le_normalizer_yamadaY₂ d hlay ⟨l, hl, rfl⟩))

theorem leviLong_map_le_normalizer_yamadaM₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    d.leviLong.map L.subtype ≤ normalizer (yamadaM₃ d t : Set G) := fun _ hl =>
  mem_normalizer_inf_D4 (h.leviLong_map_le_normalizer_yamadaL₃ d hl)
    (mem_normalizer_centralizer_D4 (h.leviLong_map_le_normalizer_yamadaY₂ d hlay hl))

theorem eq_one_of_mem_yamadaY₂_of_conj_leviThree (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {y : G}
    (hy : y ∈ yamadaY₂ d t)
    (hg : ((d.leviThree : L) : G) * y * ((d.leviThree : L) : G)⁻¹ = y) : y = 1 := by
  have h592 := h.yamada_5_9_2 d hlay
  have hgt : ((d.leviThree : L) : G) * t = t * ((d.leviThree : L) : G) :=
    mem_centralizer_singleton_iff.1 (h.L_le_centralizer d.leviThree.2)
  have hYfix : ∀ k ∈ d.Y.map L.subtype,
      ((d.leviThree : L) : G) * k * ((d.leviThree : L) : G)⁻¹ = k → k = 1 := by
    rintro _ ⟨k, hk, rfl⟩ hk'
    rw [d.eq_one_of_mem_Y_of_leviThree_conj hk (Subtype.ext hk'), map_one]
  have hc := h.commutator_t_mem_Y_of_mem_yamadaY₂ d hlay hy
  have hcfix : ((d.leviThree : L) : G) * ⁅y, t⁆ * ((d.leviThree : L) : G)⁻¹ = ⁅y, t⁆ := by
    have hgt' : ((d.leviThree : L) : G) * t * ((d.leviThree : L) : G)⁻¹ = t := by
      rw [hgt, mul_inv_cancel_right]
    rw [commutatorElement_def]
    calc ((d.leviThree : L) : G) * (y * t * y⁻¹ * t⁻¹) * ((d.leviThree : L) : G)⁻¹ =
        (((d.leviThree : L) : G) * y * ((d.leviThree : L) : G)⁻¹) *
          (((d.leviThree : L) : G) * t * ((d.leviThree : L) : G)⁻¹) *
          (((d.leviThree : L) : G) * y * ((d.leviThree : L) : G)⁻¹)⁻¹ *
          (((d.leviThree : L) : G) * t * ((d.leviThree : L) : G)⁻¹)⁻¹ := by group
      _ = y * t * y⁻¹ * t⁻¹ := by rw [hg, hgt']
  have hyt : y ∈ centralizer ({t} : Set G) :=
    mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1 (hYfix _ hc hcfix))
  have hyY : y ∈ d.Y.map L.subtype := by
    rw [← h592.2.2.2.2]
    exact Subgroup.mem_inf.2 ⟨hy, hyt⟩
  exact hYfix y hyY hg

theorem exists_x₄_of_mem_yamadaW₂_of_conj_leviThree (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {w : G}
    (hw : w ∈ yamadaW₂ d t)
    (hg : ((d.leviThree : L) : G) * w * ((d.leviThree : L) : G)⁻¹ = w) :
    ∃ c : d.Γ, w = ((d.x₄ c : L) : G) := by
  have h592 := h.yamada_5_9_2 d hlay
  have hw' : w ∈ ((d.W.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) : Set G) := hw
  rw [coe_mul_of_right_le_normalizer_left _ _ (yamadaY₂_le_normalizer_W d h592)] at hw'
  obtain ⟨_, ⟨w₀, hw₀, rfl⟩, y, hy, e⟩ := hw'
  obtain ⟨c, n, hn, rfl⟩ := d.mem_W_iff.1 hw₀
  have hny : ((n : L) : G) * y ∈ yamadaY₂ d t := mul_mem (Y_le_yamadaY₂ d h592 ⟨n, hn, rfl⟩) hy
  have hgx₄ : ((d.x₄ c : L) : G) * ((d.leviThree : L) : G) =
      ((d.leviThree : L) : G) * ((d.x₄ c : L) : G) :=
    mem_centralizer_iff.1 (leviLong_map_le_centralizer_U₄ d ⟨_, d.leviThree_mem_leviLong, rfl⟩)
      _ ⟨d.x₄ c, d.x₄_mem_U₄ c, rfl⟩
  have e1 : w = ((d.x₄ c : L) : G) * (((n : L) : G) * y) := by
    rw [← e]
    simp only [map_mul, Subgroup.coe_subtype, mul_assoc]
  have hfix : ((d.leviThree : L) : G) * (((n : L) : G) * y) * ((d.leviThree : L) : G)⁻¹ =
      ((n : L) : G) * y := by
    rw [e1] at hg
    have e2 : ((d.leviThree : L) : G) * (((d.x₄ c : L) : G) * (((n : L) : G) * y)) *
        ((d.leviThree : L) : G)⁻¹ = ((d.x₄ c : L) : G) * (((d.leviThree : L) : G) *
          (((n : L) : G) * y) * ((d.leviThree : L) : G)⁻¹) := by
      rw [← mul_assoc ((d.leviThree : L) : G), ← hgx₄]
      group
    rw [e2] at hg
    exact mul_left_cancel hg
  refine ⟨c, ?_⟩
  rw [e1, h.eq_one_of_mem_yamadaY₂_of_conj_leviThree d hlay hny hfix, mul_one]

theorem commute_x₄_of_mem_yamadaM₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {b : G}
    (hb : b ∈ yamadaM₃ d t) (hbg : b * ((d.leviThree : L) : G) = ((d.leviThree : L) : G) * b)
    (c : d.Γ) : b * ((d.x₄ c : L) : G) = ((d.x₄ c : L) : G) * b := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have hbT : b ∈ translationsW₂ d t :=
    (h.yamadaL₃_eq_translationsW₂ d hNH h561 h562 h591 h592 h593 h5101 h5102) ▸
      (Subgroup.mem_inf.1 hb).1
  have hbE := ((h.mem_centralizerW₂Y₂_iff d hNH h561 h562 h591 h592 h593 h5101 h5102).1
    ((h.mem_translationsW₂_iff d hNH h561 h562 h591 h592 h593 h5101 h5102).1 hbT).1).2
  have hXW₂ : ((d.x₄ c : L) : G) ∈ yamadaW₂ d t := mem_sup_left ⟨d.x₄ c, d.x₄_mem_W c, rfl⟩
  have hgX : ((d.x₄ c : L) : G) * ((d.leviThree : L) : G) =
      ((d.leviThree : L) : G) * ((d.x₄ c : L) : G) :=
    mem_centralizer_iff.1 (leviLong_map_le_centralizer_U₄ d ⟨_, d.leviThree_mem_leviLong, rfl⟩)
      _ ⟨d.x₄ c, d.x₄_mem_U₄ c, rfl⟩
  have hgb : ((d.leviThree : L) : G) * b * ((d.leviThree : L) : G)⁻¹ = b := by
    rw [← hbg, mul_inv_cancel_right]
  have hgX' : ((d.leviThree : L) : G) * ((d.x₄ c : L) : G) * ((d.leviThree : L) : G)⁻¹ =
      ((d.x₄ c : L) : G) := by
    rw [← hgX, mul_inv_cancel_right]
  have hfix : ((d.leviThree : L) : G) * (b * ((d.x₄ c : L) : G) * b⁻¹ * ((d.x₄ c : L) : G)⁻¹) *
      ((d.leviThree : L) : G)⁻¹ = b * ((d.x₄ c : L) : G) * b⁻¹ * ((d.x₄ c : L) : G)⁻¹ := by
    calc ((d.leviThree : L) : G) * (b * ((d.x₄ c : L) : G) * b⁻¹ * ((d.x₄ c : L) : G)⁻¹) *
          ((d.leviThree : L) : G)⁻¹ =
        (((d.leviThree : L) : G) * b * ((d.leviThree : L) : G)⁻¹) *
          (((d.leviThree : L) : G) * ((d.x₄ c : L) : G) * ((d.leviThree : L) : G)⁻¹) *
          (((d.leviThree : L) : G) * b * ((d.leviThree : L) : G)⁻¹)⁻¹ *
          (((d.leviThree : L) : G) * ((d.x₄ c : L) : G) * ((d.leviThree : L) : G)⁻¹)⁻¹ := by
          group
      _ = b * ((d.x₄ c : L) : G) * b⁻¹ * ((d.x₄ c : L) : G)⁻¹ := by rw [hgb, hgX']
  have h1 := h.eq_one_of_mem_yamadaY₂_of_conj_leviThree d hlay (hbE _ hXW₂) hfix
  calc b * ((d.x₄ c : L) : G) =
      b * ((d.x₄ c : L) : G) * b⁻¹ * ((d.x₄ c : L) : G)⁻¹ * (((d.x₄ c : L) : G) * b) := by
        group
    _ = ((d.x₄ c : L) : G) * b := by rw [h1, one_mul]

theorem mem_yamadaW₃_of_mem_yamadaM₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {b : G}
    (hb : b ∈ yamadaM₃ d t) (hbg : b * ((d.leviThree : L) : G) = ((d.leviThree : L) : G) * b) :
    b ∈ yamadaW₃ d t := by
  have h592 := h.yamada_5_9_2 d hlay
  have hbY₂ := (Subgroup.mem_inf.1 hb).2
  have hle : yamadaW₂ d t ≤ centralizer ({b} : Set G) := by
    refine sup_le ?_ fun y hy => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hbY₂ y hy)
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨c, n, hn, rfl⟩ := d.mem_W_iff.1 hw
    rw [map_mul]
    refine mul_mem (mem_centralizer_singleton_iff.2
      (h.commute_x₄_of_mem_yamadaM₃ d hlay hb hbg c).symm) ?_
    exact mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 hbY₂ _ (Y_le_yamadaY₂ d h592 ⟨n, hn, rfl⟩))
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hb).1,
    mem_centralizer_iff.2 fun w hw => mem_centralizer_singleton_iff.1 (hle hw)⟩

theorem inv_mul_conj_mem_yamadaM₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {a x : G}
    (ha : a ∈ d.leviLong.map L.subtype) (hx : x ∈ yamadaM₃ d t) :
    x⁻¹ * (a * x * a⁻¹) ∈ yamadaM₂ d t := by
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
  have haN : a ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
    obtain ⟨l, hl, rfl⟩ := ha
    exact Subgroup.mem_inf.2 ⟨h.L_le_centralizer l.2,
      coe_mem_normalizer_map (d.leviLong_le_normalizer_Y hl)⟩
  have hxL : x ∈ yamadaL₃ d t := (Subgroup.mem_inf.1 hx).1
  obtain ⟨hw, ex⟩ := hφ ⟨x, hxL⟩
  obtain ⟨hax, haw, eax⟩ := hφeq a haN ⟨x, hxL⟩
  have key : φ (QuotientGroup.mk ⟨x, hxL⟩) = φ (QuotientGroup.mk ⟨a * x * a⁻¹, hax⟩) := by
    rw [ex, eax, QuotientGroup.eq, mem_subgroupOf]
    show (t * x * t * x⁻¹)⁻¹ * (a * (t * x * t * x⁻¹) * a⁻¹) ∈ d.Y.map L.subtype
    obtain ⟨w, hwW, hwe⟩ := id hw
    obtain ⟨c, n, hn, rfl⟩ := d.mem_W_iff.1 hwW
    rw [← hwe]
    simp only [map_mul, Subgroup.coe_subtype]
    have hcx : ((d.x₄ c : L) : G) * a = a * ((d.x₄ c : L) : G) :=
      mem_centralizer_iff.1 (leviLong_map_le_centralizer_U₄ d ha) _ ⟨d.x₄ c, d.x₄_mem_U₄ c, rfl⟩
    have hac : a * ((d.x₄ c : L) : G) * a⁻¹ = ((d.x₄ c : L) : G) := by
      rw [← hcx, mul_inv_cancel_right]
    have e : (((d.x₄ c : L) : G) * ((n : L) : G))⁻¹ *
        (a * (((d.x₄ c : L) : G) * ((n : L) : G)) * a⁻¹) =
        ((n : L) : G)⁻¹ * (a * ((n : L) : G) * a⁻¹) := by
      calc (((d.x₄ c : L) : G) * ((n : L) : G))⁻¹ *
            (a * (((d.x₄ c : L) : G) * ((n : L) : G)) * a⁻¹) =
          ((n : L) : G)⁻¹ * ((d.x₄ c : L) : G)⁻¹ * (a * ((d.x₄ c : L) : G) * a⁻¹) *
            (a * ((n : L) : G) * a⁻¹) := by group
        _ = ((n : L) : G)⁻¹ * (a * ((n : L) : G) * a⁻¹) := by rw [hac]; group
    rw [e]
    exact mul_mem (inv_mem ⟨n, hn, rfl⟩)
      ((mem_normalizer_iff.1 (Subgroup.mem_inf.1 haN).2 _).1 ⟨n, hn, rfl⟩)
  have h1 := QuotientGroup.eq.1 (φ.injective key)
  rw [mem_subgroupOf] at h1
  have h2 : x⁻¹ * (a * x * a⁻¹) ∈ centralizer (yamadaY₂ d t : Set G) :=
    mul_mem (inv_mem (Subgroup.mem_inf.1 hx).2) (Subgroup.mem_inf.1
      ((mem_normalizer_iff.1 (h.leviLong_map_le_normalizer_yamadaM₃ d hlay ha) x).1 hx)).2
  rw [h.yamadaM₂_eq_inf_centralizer d h591 h592]
  exact Subgroup.mem_inf.2 ⟨h1, h2⟩

theorem yamadaM₂_sup_centralizer_leviThree (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaM₂ d t ⊔ (yamadaM₃ d t ⊓
      centralizer ((zpowers ((d.leviThree : L) : G) : Subgroup G) : Set G)) = yamadaM₃ d t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have h5171 := h.yamada_5_17_1 d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hM₂M₃ := h.yamadaM₂_le_yamadaM₃ d hlay
  have hgL : ((d.leviThree : L) : G) ∈ d.leviLong.map L.subtype :=
    ⟨_, d.leviThree_mem_leviLong, rfl⟩
  have hAL : zpowers ((d.leviThree : L) : G) ≤ d.leviLong.map L.subtype := (zpowers_le).2 hgL
  have hM₃N : yamadaM₃ d t ≤ normalizer (yamadaM₂ d t : Set G) := fun x hx =>
    h5171.2.2.1 (yamadaL₃_le_normalizer_yamadaL₂ d (Subgroup.mem_inf.1 hx).1)
  have hM₂p : IsPGroup 2 (yamadaM₂ d t) :=
    (LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le
      (le_sup_left.trans (le_of_eq h591.1.symm) : yamadaM₂ d t ≤ yamadaL₂ d t)
  have hA3 : Nat.card (zpowers ((d.leviThree : L) : G)) = 3 := by
    rw [Nat.card_zpowers]
    refine orderOf_eq_prime ?_ fun h1 => d.leviThree_ne_one (Subtype.ext h1)
    have := congrArg Subtype.val d.leviThree_pow_three
    rwa [Subgroup.coe_pow, OneMemClass.coe_one] at this
  have hcard := card_inf_centralizer_eq_of_coprime_D4 (p := 2) hM₂M₃ hM₃N
    (hAL.trans (h.leviLong_map_le_normalizer_yamadaM₃ d hlay))
    (hAL.trans (h.leviLong_map_le_normalizer_yamadaM₂ d hlay)) hM₂p (by rw [hA3]; norm_num)
    (fun a ha x hx => h.inv_mul_conj_mem_yamadaM₂ d hlay (hAL ha) hx)
  set B := yamadaM₃ d t ⊓ centralizer ((zpowers ((d.leviThree : L) : G) : Subgroup G) : Set G)
    with hB
  have hBN : B ≤ normalizer (yamadaM₂ d t : Set G) := inf_le_left.trans hM₃N
  have h1 := card_sup_mul_card_inf_eq_D4 hBN
  have hinf : yamadaM₂ d t ⊓ B = yamadaM₂ d t ⊓
      centralizer ((zpowers ((d.leviThree : L) : G) : Subgroup G) : Set G) := by
    rw [hB, ← inf_assoc, inf_eq_left.2 hM₂M₃]
  have hrel := Subgroup.relIndex_mul_card (yamadaM₂ d t) (yamadaM₃ d t)
  rw [inf_eq_left.2 hM₂M₃] at hrel
  have hpos : 0 < Nat.card (yamadaM₂ d t ⊓
      centralizer ((zpowers ((d.leviThree : L) : G) : Subgroup G) : Set G) : Subgroup G) :=
    Nat.card_pos
  have hsup : Nat.card (yamadaM₂ d t ⊔ B : Subgroup G) = Nat.card (yamadaM₃ d t) := by
    rw [hinf, hcard] at h1
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1, ← hrel]
    ring
  exact eq_of_le_of_card_ge (sup_le hM₂M₃ inf_le_left) hsup.ge

theorem yamadaM₂_sup_yamadaW₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaM₂ d t ⊔ yamadaW₃ d t = yamadaM₃ d t := by
  have hW₃M₃ : yamadaW₃ d t ≤ yamadaM₃ d t := fun x hx =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1,
      centralizer_le (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) (Subgroup.mem_inf.1 hx).2⟩
  have hBW₃ : yamadaM₃ d t ⊓ centralizer ((zpowers ((d.leviThree : L) : G) : Subgroup G) :
      Set G) ≤ yamadaW₃ d t := fun b hb =>
    h.mem_yamadaW₃_of_mem_yamadaM₃ d hlay (Subgroup.mem_inf.1 hb).1
      (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hb).2 _ (mem_zpowers _)).symm
  refine le_antisymm (sup_le (h.yamadaM₂_le_yamadaM₃ d hlay) hW₃M₃) ?_
  exact (h.yamadaM₂_sup_centralizer_leviThree d hlay).symm.le.trans
    (sup_le_sup_left hBW₃ _)

theorem yamadaM₂_inf_yamadaW₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaM₂ d t ⊓ yamadaW₃ d t = yamadaW₂ d t := by
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have hL₂L₃ := h.yamadaL₂_le_yamadaL₃ d (h.normalizerHyp_of_layerHyp d hlay) (h.yamada_5_6_1 d
    hlay)
    (h.yamada_5_6_2 d hlay) h591 h592 (h.yamada_5_9_3 d hlay) (h.yamada_5_10_1 d hlay)
    (h.yamada_5_10_2 d hlay)
  have hW₂M₂ : yamadaW₂ d t ≤ yamadaM₂ d t :=
    sup_le_sup_right (map_mono (d.W_le_F.trans d.F_le_M)) _
  have hM₂L₂ : yamadaM₂ d t ≤ yamadaL₂ d t := le_sup_left.trans (le_of_eq h591.1.symm)
  have hW₂W₃ : yamadaW₂ d t ≤ yamadaW₃ d t := fun w hw =>
    Subgroup.mem_inf.2 ⟨hL₂L₃ (hM₂L₂ (hW₂M₂ hw)),
      mem_centralizer_iff.2 fun w' hw' => yamadaW₂_mul_comm d h592 hw' hw⟩
  refine le_antisymm (fun x hx => ?_) (le_inf hW₂M₂ hW₂W₃)
  obtain ⟨hxM₂, hxW₃⟩ := Subgroup.mem_inf.1 hx
  have hxC := (Subgroup.mem_inf.1 hxW₃).2
  have hx' : x ∈ ((d.M.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) : Set G) := hxM₂
  rw [coe_mul_of_left_le_normalizer_right _ _ (M_le_normalizer_yamadaY₂ d h592)] at hx'
  obtain ⟨_, ⟨m, hm, rfl⟩, y, hy, e⟩ := hx'
  have em : ((m : L) : G) = x * y⁻¹ := eq_mul_inv_of_mul_eq e
  have hyW₂ : y ∈ yamadaW₂ d t := mem_sup_right hy
  have hmW : m ∈ d.W := d.mem_W_of_mem_M_of_commute hm fun w hw => by
    have hwW₂ : ((w : L) : G) ∈ yamadaW₂ d t := mem_sup_left ⟨w, hw, rfl⟩
    have hxw : ((w : L) : G) * x = x * ((w : L) : G) := mem_centralizer_iff.1 hxC _ hwW₂
    have hyw : ((w : L) : G) * y = y * ((w : L) : G) := yamadaW₂_mul_comm d h592 hwW₂ hyW₂
    apply Subtype.ext
    show ((m : L) : G) * ((w : L) : G) = ((w : L) : G) * ((m : L) : G)
    rw [em]
    calc x * y⁻¹ * ((w : L) : G) = x * (y⁻¹ * (((w : L) : G) * y)) * y⁻¹ := by group
      _ = x * (y⁻¹ * (y * ((w : L) : G))) * y⁻¹ := by rw [hyw]
      _ = x * ((w : L) : G) * y⁻¹ := by group
      _ = ((w : L) : G) * x * y⁻¹ := by rw [← hxw]
      _ = ((w : L) : G) * (x * y⁻¹) := by group
  rw [← e]
  exact mul_mem (mem_sup_left ⟨m, hmW, rfl⟩) (mem_sup_right hy)

theorem card_yamadaW₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    Nat.card (yamadaW₃ d t) = (2 ^ f) ^ 10 := by
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h5171 := h.yamada_5_17_1 d hNH (h.yamada_5_6_1 d hlay) (h.yamada_5_6_2 d hlay) h591
    h592 (h.yamada_5_9_3 d hlay) (h.yamada_5_10_1 d hlay) (h.yamada_5_10_2 d hlay)
  have hW₃N : yamadaW₃ d t ≤ normalizer (yamadaM₂ d t : Set G) := fun x hx =>
    h5171.2.2.1 (yamadaL₃_le_normalizer_yamadaL₂ d (Subgroup.mem_inf.1 hx).1)
  have h1 := card_sup_mul_card_inf_eq_D4 hW₃N
  rw [h.yamadaM₂_sup_yamadaW₃ d hlay, h.yamadaM₂_inf_yamadaW₃ d hlay,
    h.card_yamadaM₃ d hlay, h.card_yamadaW₂ d h592, (h.card_yamadaM₂_and d hlay).1] at h1
  refine Nat.eq_of_mul_eq_mul_left (n := (2 ^ f) ^ 13) (by positivity) ?_
  rw [← h1]
  ring

end Three

section Elem

theorem yamadaL₃_le_normalizer_yamadaW₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaL₃ d t ≤ normalizer (yamadaW₃ d t : Set G) := fun g hg => by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  exact mem_normalizer_inf_D4 (le_normalizer hg) (mem_normalizer_centralizer_D4
    ((h.normalizer_yamadaV₂_le d h562 h592).1 (h.yamadaL₃_le_normalizer_yamadaV₂ d hNH h561 h562
      (h.yamada_5_9_1 d hlay) h592 (h.yamada_5_9_3 d hlay) (h.yamada_5_10_1 d hlay)
      (h.yamada_5_10_2 d hlay) hg)))

theorem exists_mul_self_eq_x₄_of_mem_yamadaW₃ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {x : G}
    (hx : x ∈ yamadaW₃ d t) : ∃ c : d.Γ, x * x = ((d.x₄ c : L) : G) := by
  have h562 := h.yamada_5_6_2 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h5171 := h.yamada_5_17_1 d hNH (h.yamada_5_6_1 d hlay) h562 (h.yamada_5_9_1 d hlay)
    h592 (h.yamada_5_9_3 d hlay) (h.yamada_5_10_1 d hlay) (h.yamada_5_10_2 d hlay)
  have hBN : yamadaM₃ d t ⊓ centralizer ((zpowers ((d.leviThree : L) : G) : Subgroup G) :
      Set G) ≤ normalizer (yamadaM₂ d t : Set G) := fun x hx =>
    h5171.2.2.1 (yamadaL₃_le_normalizer_yamadaL₂ d (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).1)
  have hxM₃ : x ∈ ((yamadaM₂ d t ⊔ (yamadaM₃ d t ⊓
      centralizer ((zpowers ((d.leviThree : L) : G) : Subgroup G) : Set G)) : Subgroup G) :
        Set G) := by
    rw [h.yamadaM₂_sup_centralizer_leviThree d hlay]
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1,
      centralizer_le (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) (Subgroup.mem_inf.1 hx).2⟩
  rw [coe_mul_of_right_le_normalizer_left _ _ hBN] at hxM₃
  obtain ⟨n, hn, b, hb, e⟩ := hxM₃
  have hbg : b * ((d.leviThree : L) : G) = ((d.leviThree : L) : G) * b :=
    (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hb).2 _ (mem_zpowers _)).symm
  have hbW₃ := h.mem_yamadaW₃_of_mem_yamadaM₃ d hlay (Subgroup.mem_inf.1 hb).1 hbg
  have hnW₂ : n ∈ yamadaW₂ d t := by
    rw [← h.yamadaM₂_inf_yamadaW₃ d hlay]
    refine Subgroup.mem_inf.2 ⟨hn, ?_⟩
    have := mul_mem hx (inv_mem hbW₃)
    rwa [← e, mul_inv_cancel_right] at this
  have hbn : n * b = b * n := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hbW₃).2 n hnW₂
  have hxx : x * x = b * b := by
    rw [← e]
    calc n * b * (n * b) = (n * n) * (b * b) := by
          rw [show n * b * (n * b) = n * (b * n) * b by group, ← hbn]
          group
      _ = b * b := by rw [yamadaW₂_mul_self d h562 h592 hnW₂, one_mul]
  have hbbW₂ : b * b ∈ yamadaW₂ d t :=
    h.mul_self_mem_yamadaW₂_of_mem_yamadaL₃ d hlay (Subgroup.mem_inf.1 hbW₃).1
  have hfix : ((d.leviThree : L) : G) * (b * b) * ((d.leviThree : L) : G)⁻¹ = b * b := by
    calc ((d.leviThree : L) : G) * (b * b) * ((d.leviThree : L) : G)⁻¹ =
        (((d.leviThree : L) : G) * b) * b * ((d.leviThree : L) : G)⁻¹ := by group
      _ = (b * ((d.leviThree : L) : G)) * b * ((d.leviThree : L) : G)⁻¹ := by rw [← hbg]
      _ = b * (((d.leviThree : L) : G) * b) * ((d.leviThree : L) : G)⁻¹ := by group
      _ = b * (b * ((d.leviThree : L) : G)) * ((d.leviThree : L) : G)⁻¹ := by rw [← hbg]
      _ = b * b := by group
  obtain ⟨c, hc⟩ := h.exists_x₄_of_mem_yamadaW₂_of_conj_leviThree d hlay hbbW₂ hfix
  exact ⟨c, hxx.trans hc⟩

theorem mul_self_eq_one_of_mem_yamadaW₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G}
    (hx : x ∈ yamadaW₃ d t) : x * x = 1 := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have hL₂L₃ := h.yamadaL₂_le_yamadaL₃ d hNH (h.yamada_5_6_1 d hlay) (h.yamada_5_6_2 d hlay)
    (h.yamada_5_9_1 d hlay) (h.yamada_5_9_2 d hlay) (h.yamada_5_9_3 d hlay)
    (h.yamada_5_10_1 d hlay) (h.yamada_5_10_2 d hlay)
  have hML₃ : d.M.map L.subtype ≤ yamadaL₃ d t :=
    (le_sup_left.trans (h.tM_le_yamadaL₂ d)).trans hL₂L₃
  obtain ⟨c, hc⟩ := h.exists_mul_self_eq_x₄_of_mem_yamadaW₃ d hlay hx
  suffices hc0 : c = 0 by
    rw [hc, hc0, d.x₄_zero]
    rfl
  apply d.eq_zero_of_forall_tr_mul
  intro a
  rw [mul_comm]
  have hs : ((d.x₁ a : L) : G) ∈ yamadaL₃ d t := hML₃ ⟨d.x₁ a, d.x₁_mem_M a, rfl⟩
  have hsx : ((d.x₁ a : L) : G) * x * ((d.x₁ a : L) : G)⁻¹ ∈ yamadaW₃ d t :=
    (mem_normalizer_iff.1 (h.yamadaL₃_le_normalizer_yamadaW₃ d hlay hs) x).1 hx
  obtain ⟨c', hc'⟩ := h.exists_mul_self_eq_x₄_of_mem_yamadaW₃ d hlay hsx
  have hconjL : d.x₁ a * d.x₄ c * (d.x₁ a)⁻¹ = d.x₅ (d.tr (a * c)) * d.x₄ c := by
    rw [conj_eq_commutatorElement_mul, d.comm₁₄]
  have hconj : ((d.x₁ a : L) : G) * ((d.x₄ c : L) : G) * ((d.x₁ a : L) : G)⁻¹ =
      ((d.x₅ (d.tr (a * c)) : L) : G) * ((d.x₄ c : L) : G) := by
    have := congrArg Subtype.val hconjL
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  have e : ((d.x₁ a : L) : G) * x * ((d.x₁ a : L) : G)⁻¹ *
      (((d.x₁ a : L) : G) * x * ((d.x₁ a : L) : G)⁻¹) =
      ((d.x₅ (d.tr (a * c)) : L) : G) * ((d.x₄ c : L) : G) := by
    rw [show ((d.x₁ a : L) : G) * x * ((d.x₁ a : L) : G)⁻¹ *
      (((d.x₁ a : L) : G) * x * ((d.x₁ a : L) : G)⁻¹) =
      ((d.x₁ a : L) : G) * (x * x) * ((d.x₁ a : L) : G)⁻¹ by group, hc, hconj]
  rw [e] at hc'
  have hL : d.x₅ (d.tr (a * c)) * d.x₄ c = d.x₄ c' := Subtype.ext hc'
  have h5 : d.x₅ (d.tr (a * c)) ∈ d.U₄ :=
    ⟨c' + c, by rw [d.x₄_add, ← hL, mul_assoc, d.x₄_mul_self, mul_one]⟩
  exact d.eq_zero_of_x₅_mem_U₄ h5

theorem yamadaW₃_le_yamadaC₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaW₃ d t ≤ yamadaC₅ d t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h512 := (h.yamada_5_12 d hNH h561 h562 h591 h592 h593).2.1.2.2
  intro x hx
  have hxR₅ : x ∈ yamadaR₅ d t :=
    (Subgroup.mem_inf.1 (h.yamadaL₃_le_yamadaR₃_D3 d hlay (Subgroup.mem_inf.1 hx).1)).1
  have hxC := (Subgroup.mem_inf.1 hx).2
  have hx' : x ∈ ((yamadaR₅ d t : Subgroup G) : Set G) := hxR₅
  rw [h.coe_yamadaR₅ d] at hx'
  obtain ⟨c, hc, _, ⟨s, hs, rfl⟩, e⟩ := hx'
  have es : ((s : L) : G) = c⁻¹ * x := by
    rw [← e]
    simp only [Subgroup.coe_subtype, inv_mul_cancel_left]
  have hsD : s ∈ d.D := d.mem_D_of_commutatorElement_mem_V hs fun w hw => by
    have hwD₁ : ((w : L) : G) ∈ yamadaD₁ d t :=
      D_le_yamadaD₁ d t ⟨w, (d.W_le_F.trans d.F_le_D) hw, rfl⟩
    have hcw := h512 c⁻¹ (inv_mem hc) _ hwD₁
    have hxw : ((w : L) : G) * x = x * ((w : L) : G) :=
      mem_centralizer_iff.1 hxC _ (mem_sup_left ⟨w, hw, rfl⟩)
    have e2 : ((s * w * s⁻¹ * w⁻¹ : L) : G) =
        c⁻¹ * ((w : L) : G) * c⁻¹⁻¹ * ((w : L) : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, es]
      calc c⁻¹ * x * ((w : L) : G) * (c⁻¹ * x)⁻¹ * ((w : L) : G)⁻¹ =
          c⁻¹ * (x * ((w : L) : G)) * x⁻¹ * c * ((w : L) : G)⁻¹ := by group
        _ = c⁻¹ * (((w : L) : G) * x) * x⁻¹ * c * ((w : L) : G)⁻¹ := by rw [hxw]
        _ = c⁻¹ * ((w : L) : G) * c⁻¹⁻¹ * ((w : L) : G)⁻¹ := by group
    have hmem : ((s * w * s⁻¹ * w⁻¹ : L) : G) ∈ yamadaV₁ d t ⊓ d.D.map L.subtype := by
      refine Subgroup.mem_inf.2 ⟨by rw [e2]; exact hcw, ⟨s * w * s⁻¹ * w⁻¹, ?_, rfl⟩⟩
      exact (d.W_le_F.trans d.F_le_D)
        (mul_mem ((mem_normalizer_iff.1 (d.S_le_normalizer_W hs) w).1 hw) (inv_mem hw))
    rw [h.yamadaV₁_inf_D d h562] at hmem
    obtain ⟨z, hz, hze⟩ := hmem
    rwa [← Subtype.ext hze]
  rw [← e]
  exact mul_mem hc ((h.D_map_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t) ⟨s, hsD, rfl⟩)

theorem yamadaW₃_le_yamadaF₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaW₃ d t ≤ yamadaF₃ d t := fun x hx => by
  obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxY₂ : x ∈ centralizer (yamadaY₂ d t : Set G) :=
    centralizer_le (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) hxC
  have hxV₁ : x ∈ centralizer (yamadaV₁ d t : Set G) := centralizer_le (yamadaV₁_le_yamadaY₂ d) hxY₂
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hxL, hxY₂⟩, Subgroup.mem_inf.2
    ⟨Subgroup.mem_inf.2 ⟨h.yamadaL₃_le_yamadaR₃_D3 d hlay hxL, hxV₁⟩,
      h.yamadaW₃_le_yamadaC₅ d hlay hx⟩⟩

theorem v_mem_normalizer_yamadaW₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    ((d.v : L) : G) ∈ normalizer (yamadaW₃ d t : Set G) :=
  mem_normalizer_inf_D4 (h.v_mem_normalizer_yamadaL₃ d) (mem_normalizer_centralizer_D4
    (mem_normalizer_sup (coe_mem_normalizer_map (d.leviLong_le_normalizer_W d.v_mem_leviLong))
      (v_mem_normalizer_yamadaY₂ d)))

theorem inf_conj_v_le_yamadaW₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaF₃ d t ⊓ (yamadaF₃ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom ≤
      yamadaW₃ d t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h512 := (h.yamada_5_12 d hNH h561 h562 h591 h592 h593).2.1.2.2
  have hF₃C₅ : yamadaF₃ d t ≤ yamadaC₅ d t := fun y hy =>
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hy).2).2
  have hvW : ((d.v : L) : G) ∈ normalizer ((d.W.map L.subtype : Subgroup G) : Set G) :=
    coe_mem_normalizer_map (d.leviLong_le_normalizer_W d.v_mem_leviLong)
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
  rw [mem_map_conj_iff_D4] at hx₂
  have hxM₃ : x ∈ yamadaM₃ d t := (Subgroup.mem_inf.1 hx₁).1
  have hle : yamadaW₂ d t ≤ centralizer ({x} : Set G) := by
    refine sup_le (fun w hw => ?_) fun y hy =>
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hxM₃).2 y hy)
    have hwD : w ∈ yamadaD₁ d t := D_le_yamadaD₁ d t (map_mono (d.W_le_F.trans d.F_le_D) hw)
    have h1 := h512 x (hF₃C₅ hx₁) w hwD
    have hw' : ((d.v : L) : G)⁻¹ * w * ((d.v : L) : G) ∈ d.W.map L.subtype := by
      have := (mem_normalizer_iff.1 (inv_mem hvW) w).1 hw
      rwa [inv_inv] at this
    have h2 := h512 _ (hF₃C₅ hx₂) _
      (D_le_yamadaD₁ d t (map_mono (d.W_le_F.trans d.F_le_D) hw'))
    have h3 : x * w * x⁻¹ * w⁻¹ ∈
        (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom := by
      rw [mem_map_conj_iff_D4]
      rw [show ((d.v : L) : G)⁻¹ * (x * w * x⁻¹ * w⁻¹) * ((d.v : L) : G) =
        (((d.v : L) : G)⁻¹ * x * ((d.v : L) : G)) * (((d.v : L) : G)⁻¹ * w * ((d.v : L) : G)) *
          (((d.v : L) : G)⁻¹ * x * ((d.v : L) : G))⁻¹ *
          (((d.v : L) : G)⁻¹ * w * ((d.v : L) : G))⁻¹ by group]
      exact h2
    have h4 : x * w * x⁻¹ * w⁻¹ ∈
        yamadaV₁ d t ⊓ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom :=
      Subgroup.mem_inf.2 ⟨h1, h3⟩
    rw [h592.1, Subgroup.mem_bot] at h4
    refine mem_centralizer_singleton_iff.2 ?_
    calc w * x = (x * w * x⁻¹ * w⁻¹)⁻¹ * (x * w) := by group
      _ = x * w := by rw [h4, inv_one, one_mul]
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hxM₃).1,
    mem_centralizer_iff.2 fun w hw => mem_centralizer_singleton_iff.1 (hle hw)⟩

theorem yamada_5_21 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaW₃ d t = yamadaF₃ d t ⊓ (yamadaF₃ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom ∧
      IsElemAbelian 2 (yamadaW₃ d t) ∧ Nat.card (yamadaW₃ d t) = (2 ^ f) ^ 10 := by
  have hsq : ∀ x ∈ yamadaW₃ d t, x * x = 1 := fun x hx =>
    h.mul_self_eq_one_of_mem_yamadaW₃ d hlay hx
  refine ⟨le_antisymm (le_inf (h.yamadaW₃_le_yamadaF₃ d hlay) fun x hx => ?_)
    (h.inf_conj_v_le_yamadaW₃ d hlay), ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩,
    h.card_yamadaW₃ d hlay⟩
  · rw [mem_map_conj_iff_D4]
    apply h.yamadaW₃_le_yamadaF₃ d hlay
    have := (mem_normalizer_iff.1 (inv_mem (h.v_mem_normalizer_yamadaW₃ d)) x).1 hx
    rwa [inv_inv] at this
  · show (a : G) * b = b * a
    have ha' : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq _ a.2)
    have hb' : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq _ b.2)
    calc (a : G) * b = ((a : G) * b)⁻¹ :=
          (inv_eq_of_mul_eq_one_right (hsq _ (mul_mem a.2 b.2))).symm
      _ = b * a := by rw [mul_inv_rev, ha', hb']
  · rw [pow_two]
    exact hsq x hx

end Elem

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
