module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL3Three
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Eight

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

section Orders

theorem yamadaL₃_inf_S_map (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaL₃ d t ⊓ d.S.map L.subtype = d.M.map L.subtype := by
  have hL₂L₃ := h.yamadaL₂_le_yamadaL₃ d (h.normalizerHyp_of_layerHyp d hlay) (h.yamada_5_6_1 d
    hlay)
    (h.yamada_5_6_2 d hlay) (h.yamada_5_9_1 d hlay) (h.yamada_5_9_2 d hlay)
    (h.yamada_5_9_3 d hlay) (h.yamada_5_10_1 d hlay) (h.yamada_5_10_2 d hlay)
  refine le_antisymm ?_ (le_inf ((le_sup_left.trans (h.tM_le_yamadaL₂ d)).trans hL₂L₃)
    (map_mono d.M_le_S))
  rintro _ ⟨hx, s, hs, rfl⟩
  have hsY : s ∈ d.S ⊓ centralizer (d.Y : Set L) :=
    ⟨hs, mem_centralizer_iff.2 fun y hy => Subtype.ext
      (mem_centralizer_iff.1 (h.yamadaL₃_le_centralizer_Y d (h.yamada_5_9_2 d hlay)
        (h.yamada_5_20 d hlay) hx) _ ⟨y, hy, rfl⟩)⟩
  rw [d.S_inf_centralizer_Y] at hsY
  exact ⟨s, hsY, rfl⟩

theorem yamadaC₅_inf_S_map (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaC₅ d t ⊓ d.S.map L.subtype = d.D.map L.subtype := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h512 := (h.yamada_5_12 d hNH h561 h562 (h.yamada_5_9_1 d hlay)
    (h.yamada_5_9_2 d hlay) (h.yamada_5_9_3 d hlay)).2.1.2.2
  refine le_antisymm ?_ (le_inf ((h.D_map_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t))
    (map_mono d.D_le_S))
  rintro _ ⟨hc, s, hs, rfl⟩
  refine ⟨s, d.mem_D_of_commutatorElement_mem_V hs fun w hw => ?_, rfl⟩
  have hcw := h512 _ hc _ (D_le_yamadaD₁ d t ⟨w, (d.W_le_F.trans d.F_le_D) hw, rfl⟩)
  have hmem : ((s * w * s⁻¹ * w⁻¹ : L) : G) ∈ yamadaV₁ d t ⊓ d.D.map L.subtype :=
    Subgroup.mem_inf.2 ⟨hcw, ⟨s * w * s⁻¹ * w⁻¹, (d.W_le_F.trans d.F_le_D)
      (mul_mem ((mem_normalizer_iff.1 (d.S_le_normalizer_W hs) w).1 hw) (inv_mem hw)), rfl⟩⟩
  rw [h.yamadaV₁_inf_D d h562] at hmem
  obtain ⟨z, hz, hze⟩ := hmem
  rwa [← Subtype.ext hze]

theorem yamadaR₅_le_normalizer_yamadaC₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaR₅ d t ≤ normalizer (yamadaC₅ d t : Set G) :=
  sup_le le_normalizer ((h.S_le_normalizer_yamadaC₁ d).trans (le_normalizer_yamadaC₅ d t))

theorem card_yamadaR₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    Nat.card (yamadaR₃ d t) = 2 * (2 ^ f) ^ 17 := by
  have hR₃ := (h.yamada_5_17_2 d (h.normalizerHyp_of_layerHyp d hlay) (h.yamada_5_6_1 d hlay)
    (h.yamada_5_6_2 d hlay) (h.yamada_5_9_1 d hlay) (h.yamada_5_9_2 d hlay)
    (h.yamada_5_9_3 d hlay) (h.yamada_5_10_1 d hlay) (h.yamada_5_10_2 d hlay)).2
  have h1 := card_sup_mul_card_inf_eq_D4 (h.S_le_normalizer_yamadaL₃ d)
  rw [← hR₃, h.yamadaL₃_inf_S_map d hlay, Subgroup.card_subtype, Subgroup.card_subtype,
    d.card_M, d.card_S, h.card_yamadaL₃ d hlay] at h1
  refine Nat.eq_of_mul_eq_mul_right (m := (2 ^ f) ^ 11) (by positivity) ?_
  rw [h1]
  ring

theorem card_yamadaR₃_inf_yamadaC₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    Nat.card (yamadaR₃ d t ⊓ yamadaC₅ d t : Subgroup G) = 2 * (2 ^ f) ^ 14 := by
  have hR₃ := (h.yamada_5_17_2 d (h.normalizerHyp_of_layerHyp d hlay) (h.yamada_5_6_1 d hlay)
    (h.yamada_5_6_2 d hlay) (h.yamada_5_9_1 d hlay) (h.yamada_5_9_2 d hlay)
    (h.yamada_5_9_3 d hlay) (h.yamada_5_10_1 d hlay) (h.yamada_5_10_2 d hlay)).2
  have hR₃R₅ : yamadaR₃ d t ≤ yamadaR₅ d t := inf_le_left
  have hSR₃ : d.S.map L.subtype ≤ yamadaR₃ d t := hR₃ ▸ le_sup_right
  have hSC : d.S.map L.subtype ≤ normalizer (yamadaC₅ d t : Set G) :=
    (h.S_le_normalizer_yamadaC₁ d).trans (le_normalizer_yamadaC₅ d t)
  have h1 := card_sup_mul_card_inf_eq_D4 hSC
  have h2 := card_sup_mul_card_inf_eq_D4 (hR₃R₅.trans (h.yamadaR₅_le_normalizer_yamadaC₅ d))
  have hsup : yamadaC₅ d t ⊔ yamadaR₃ d t = yamadaC₅ d t ⊔ d.S.map L.subtype :=
    le_antisymm (sup_le le_sup_left hR₃R₅) (sup_le_sup_left hSR₃ _)
  rw [hsup, inf_comm, h.card_yamadaR₃ d hlay] at h2
  rw [h.yamadaC₅_inf_S_map d hlay, Subgroup.card_subtype, Subgroup.card_subtype, d.card_D,
    d.card_S] at h1
  have hC₅pos : 0 < Nat.card (yamadaC₅ d t) := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hC₅pos (by positivity : 0 < (2 ^ f) ^ 12)) ?_
  calc Nat.card (yamadaC₅ d t) * (2 ^ f) ^ 12 *
        Nat.card (yamadaR₃ d t ⊓ yamadaC₅ d t : Subgroup G) =
      Nat.card (yamadaC₅ d t ⊔ d.S.map L.subtype : Subgroup G) * (2 ^ f) ^ 9 *
        Nat.card (yamadaR₃ d t ⊓ yamadaC₅ d t : Subgroup G) := by rw [h1]
    _ = Nat.card (yamadaC₅ d t ⊔ d.S.map L.subtype : Subgroup G) *
        Nat.card (yamadaR₃ d t ⊓ yamadaC₅ d t : Subgroup G) * (2 ^ f) ^ 9 := by ring
    _ = Nat.card (yamadaC₅ d t) * (2 * (2 ^ f) ^ 17) * (2 ^ f) ^ 9 := by rw [h2]
    _ = Nat.card (yamadaC₅ d t) * (2 ^ f) ^ 12 * (2 * (2 ^ f) ^ 14) := by ring

end Orders

section Derived

theorem commutator_yamadaR₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    ⁅yamadaR₃ d t, yamadaR₃ d t⁆ = yamadaF₂ d t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have hR₃ := (h.yamada_5_17_2 d hNH h561 h562 h591 h592 h593 h5101 h5102).2
  have hL₂L₃ := h.yamadaL₂_le_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hML₃ : d.M.map L.subtype ≤ yamadaL₃ d t :=
    (le_sup_left.trans (h.tM_le_yamadaL₂ d)).trans hL₂L₃
  have hSR₃ : d.S.map L.subtype ≤ yamadaR₃ d t := hR₃ ▸ le_sup_right
  have hL₃R₃ : yamadaL₃ d t ≤ yamadaR₃ d t := hR₃ ▸ le_sup_left
  have hSS : ⁅d.S.map L.subtype, d.S.map L.subtype⁆ = d.F.map L.subtype := by
    rw [← map_commutator, d.commutator_S_eq]
  refine le_antisymm (fun x hx => ?_) (sup_le ?_ ?_)
  ·
    have hxL₃ : x ∈ yamadaL₃ d t := by
      have hle := commutator_sup_le_C8 (h.S_le_normalizer_yamadaL₃ d)
        (hSS.le.trans ((map_mono d.F_le_M).trans hML₃))
      rw [← hR₃] at hle
      exact hle hx
    have hxR₂ : x ∈ yamadaR₂ d t := by
      have hW₃N : yamadaW₃ d t ≤ normalizer (yamadaR₂ d t : Set G) := fun w hw =>
        (h.yamada_5_14 d hNH h561 h562 h591 h592 h593).2.2.2.1.2
          (hL₃R₃ (Subgroup.mem_inf.1 hw).1)
      have hW₃c : ⁅yamadaW₃ d t, yamadaW₃ d t⁆ ≤ yamadaR₂ d t := by
        rw [commutator_le]
        intro a ha b hb
        have hab : a * b = b * a := by
          have := (h.yamada_5_21 d hlay).2.1.1
          exact congrArg Subtype.val (this.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
        rw [commutatorElement_eq_one_iff_mul_comm.2 hab]
        exact one_mem _
      have hle : yamadaR₃ d t ≤ yamadaR₂ d t ⊔ yamadaW₃ d t := by
        rw [hR₃, h.yamadaL₃_eq_sup d hlay, ← h.yamadaM₂_sup_yamadaW₃ d hlay]
        have hL₂R₂ : yamadaL₂ d t ≤ yamadaR₂ d t := le_sup_left
        have hM₂R₂ : yamadaM₂ d t ≤ yamadaR₂ d t :=
          (le_sup_left.trans (le_of_eq h591.1.symm)).trans hL₂R₂
        have htR₂ : zpowers t ≤ yamadaR₂ d t := (zpowers_le).2 (hL₂R₂ (h.t_mem_yamadaL₂ d))
        exact sup_le (sup_le (sup_le (hM₂R₂.trans le_sup_left) le_sup_right)
          (htR₂.trans le_sup_left)) ((le_sup_right : d.S.map L.subtype ≤ yamadaR₂ d t).trans
            le_sup_left)
      exact commutator_sup_le_C8 hW₃N hW₃c (commutator_mono hle hle hx)
    have hxC₅ : x ∈ yamadaC₅ d t := by
      have hSC : d.S.map L.subtype ≤ normalizer (yamadaC₅ d t : Set G) :=
        (h.S_le_normalizer_yamadaC₁ d).trans (le_normalizer_yamadaC₅ d t)
      have hFC : ⁅d.S.map L.subtype, d.S.map L.subtype⁆ ≤ yamadaC₅ d t :=
        hSS.le.trans ((map_mono d.F_le_D).trans
          ((h.D_map_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t)))
      have hR₃R₅ : yamadaR₃ d t ≤ yamadaR₅ d t := inf_le_left
      exact commutator_sup_le_C8 hSC hFC (commutator_mono hR₃R₅ hR₃R₅ hx)
    have hxV : x ∈ centralizer (yamadaV₁ d t : Set G) := by
      have htS₃ := h.t_mem_normalizer_yamadaS₃ d hlay
      have hzz : ⁅zpowers t, zpowers t⁆ ≤ yamadaS₃ d t := by
        rw [commutator_le]
        intro a ha b hb
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
        obtain ⟨l, rfl⟩ := mem_zpowers_iff.1 hb
        rw [commutatorElement_eq_one_iff_mul_comm.2 ((Commute.refl t).zpow_zpow k l).eq]
        exact one_mem _
      have hle := commutator_sup_le_C8 ((zpowers_le).2 htS₃) hzz
      rw [← h.yamadaR₃_eq_sup d hlay] at hle
      exact (Subgroup.mem_inf.1 (hle hx)).2
    have hxL₂ : x ∈ yamadaL₂ d t :=
      yamadaL₃_inf_le d t (Subgroup.mem_inf.2 ⟨hxL₃, h.yamadaR₂_le_normalizer_tY d hxR₂⟩)
    have hxF : x ∈ yamadaF₂ d t ⊔ zpowers t := by
      rw [← h.yamadaL₂_inf_yamadaC₅ d hlay]
      exact Subgroup.mem_inf.2 ⟨hxL₂, hxC₅⟩
    have htF₂ : t ∈ normalizer (yamadaF₂ d t : Set G) :=
      mem_normalizer_sup (h.t_mem_normalizer_map_D1 d.F) (h.t_mem_normalizer_yamadaY₂_D1 d)
    rw [h.mem_sup_zpowers_iff_of_normalizer htF₂] at hxF
    rcases hxF with hxF | hxF
    · exact hxF
    · exfalso
      apply h.t_not_mem_centralizer_yamadaV₁ d hlay
      have := mul_mem (h.yamadaF₂_le_centralizer_yamadaV₁ d hlay hxF) (inv_mem hxV)
      rwa [mul_inv_cancel_right] at this
  ·
    rw [← hSS]
    exact commutator_mono hSR₃ hSR₃
  ·
    exact (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t).trans
      ((h.yamada_5_18 d hlay).symm.le.trans (commutator_mono hL₃R₃ hL₃R₃))

theorem yamadaL₃_inf_yamadaC₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaL₃ d t ⊓ yamadaC₅ d t = yamadaF₃ d t ⊔ zpowers t := by
  have htC₅ := h.t_mem_yamadaC₅ d
  have hL₃R₃ := h.yamadaL₃_le_yamadaR₃_D3 d hlay
  have hM₃F₃ : ∀ x ∈ yamadaM₃ d t, x ∈ yamadaC₅ d t → x ∈ yamadaF₃ d t := fun x hx hxC =>
    Subgroup.mem_inf.2 ⟨hx, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hL₃R₃ (Subgroup.mem_inf.1 hx).1,
      centralizer_le (yamadaV₁_le_yamadaY₂ d) (Subgroup.mem_inf.1 hx).2⟩, hxC⟩⟩
  have htL₃ : t ∈ yamadaL₃ d t := by
    rw [h.yamadaL₃_eq_sup d hlay]
    exact mem_sup_right (mem_zpowers t)
  have htM₃ : t ∈ normalizer (yamadaM₃ d t : Set G) :=
    mem_normalizer_inf_D4 (le_normalizer htL₃)
      (mem_normalizer_centralizer_D4 (h.t_mem_normalizer_yamadaY₂_D1 d))
  refine le_antisymm (fun x hx => ?_) (sup_le (fun x hx => Subgroup.mem_inf.2
    ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).1,
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).2).2⟩)
    ((zpowers_le).2 (Subgroup.mem_inf.2 ⟨htL₃, htC₅⟩)))
  obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.1 hx
  rw [h.yamadaL₃_eq_sup d hlay, h.mem_sup_zpowers_iff_of_normalizer htM₃] at hxL
  rcases hxL with hxM | hxM
  · exact mem_sup_left (hM₃F₃ x hxM hxC)
  · have h1 := hM₃F₃ _ hxM (mul_mem htC₅ hxC)
    have e : x = t * (t * x) := by rw [← mul_assoc, h.t_mul_t, one_mul]
    rw [e]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left h1)

end Derived

section Normalizer

theorem yamadaW₃_inf_centralizer_le (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaW₃ d t ⊓ centralizer ({t} : Set G) ≤ d.W.map L.subtype := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h5171 := h.yamada_5_17_1 d hNH (h.yamada_5_6_1 d hlay) (h.yamada_5_6_2 d hlay) h591
    h592 (h.yamada_5_9_3 d hlay) (h.yamada_5_10_1 d hlay) (h.yamada_5_10_2 d hlay)
  intro x hx
  obtain ⟨hxW₃, hxt⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.1 hxW₃
  have hxY₂ : x ∈ centralizer (yamadaY₂ d t : Set G) :=
    centralizer_le (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) hxC
  have hx' : x ∈ yamadaL₃ d t ⊓ centralizer ({t} : Set G) := Subgroup.mem_inf.2 ⟨hxL, hxt⟩
  rw [h5171.2.2.2.1, h.mem_sup_zpowers_iff_of_normalizer (h.t_mem_normalizer_map_D1 d.M)] at hx'
  rcases hx' with hxM | hxM
  · obtain ⟨m, hm, rfl⟩ := hxM
    refine ⟨m, d.mem_W_of_mem_M_of_commute hm fun w hw => Subtype.ext ?_, rfl⟩
    exact (mem_centralizer_iff.1 hxC _ (mem_sup_left ⟨w, hw, rfl⟩)).symm
  · exfalso
    apply t_not_mem_centralizer_yamadaY₂ d h592
    have h1 : t * x ∈ centralizer (yamadaY₂ d t : Set G) :=
      h.M_map_le_centralizer_yamadaY₂ d hlay hxM
    have := mul_mem h1 (inv_mem hxY₂)
    rwa [mul_inv_cancel_right] at this

theorem mem_normalizer_sup_zpowers_D3 (h : Setup G L f t) {A : Subgroup G} {g : G}
    (htA : t ∈ normalizer (A : Set G)) (hgA : g ∈ normalizer (A : Set G))
    (hgt : g * t * g⁻¹ ∈ A ⊔ zpowers t) : g ∈ normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) :=
  mem_normalizer_fintype fun z hz => by
    rw [SetLike.mem_coe, h.mem_sup_zpowers_iff_of_normalizer htA] at hz
    rcases hz with hz | hz
    · exact mem_sup_left ((mem_normalizer_iff.1 hgA z).1 hz)
    · rw [show g * z * g⁻¹ = (g * t * g⁻¹) * (g * (t * z) * g⁻¹) by
        rw [show g * t * g⁻¹ * (g * (t * z) * g⁻¹) = g * (t * t) * z * g⁻¹ by group, h.t_mul_t,
          mul_one]]
      exact mul_mem hgt (mem_sup_left ((mem_normalizer_iff.1 hgA _).1 hz))

theorem yamada_5_22_2 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    normalizer ((yamadaW₃ d t ⊔ zpowers t : Subgroup G) : Set G) =
      yamadaL₃ d t ⊔ (centralizer ({t} : Set G) ⊓
        normalizer ((d.Y.map L.subtype : Subgroup G) : Set G)) := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have h5171 := h.yamada_5_17_1 d hNH h561 h562 h591 h592 h593 h5101 h5102
  have h521 := h.yamada_5_21 d hlay
  have hW₂W₃ : yamadaW₂ d t ≤ yamadaW₃ d t := by
    rw [← h.yamadaM₂_inf_yamadaW₃ d hlay]
    exact inf_le_right
  have hWW₃ : d.W.map L.subtype ≤ yamadaW₃ d t := le_sup_left.trans hW₂W₃
  have htL₃ : t ∈ yamadaL₃ d t := by
    rw [h.yamadaL₃_eq_sup d hlay]
    exact mem_sup_right (mem_zpowers t)
  have htW₃ : t ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaL₃_le_normalizer_yamadaW₃ d hlay htL₃
  have htW₃' : t ∉ yamadaW₃ d t := fun ht =>
    t_not_mem_centralizer_yamadaY₂ d h592
      (centralizer_le (le_sup_right : yamadaY₂ d t ≤ yamadaW₂ d t) (Subgroup.mem_inf.1 ht).2)
  have hWc : ∀ a ∈ yamadaW₃ d t, ∀ b ∈ yamadaW₃ d t, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h521.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsq : ∀ a ∈ yamadaW₃ d t, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact h521.2.1.2 a ha
  have hCt := h.yamadaW₃_inf_centralizer_le d hlay
  rw [← h5171.2.1, h5171.1]
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  ·
    have hgW₃ : g ∈ normalizer (yamadaW₃ d t : Set G) := by
      by_contra hne
      set H := (yamadaW₃ d t).map (MulAut.conj g).toMonoidHom with hH
      have hHK : H ≤ yamadaW₃ d t ⊔ zpowers t := by
        rintro _ ⟨w, hw, rfl⟩
        exact (mem_normalizer_iff.1 hg w).1 (mem_sup_left hw)
      have hHle : ¬ H ≤ yamadaW₃ d t := fun hle =>
        hne (mem_normalizer_fintype fun w hw => hle ⟨w, hw, rfl⟩)
      obtain ⟨y, hyH, hyW⟩ := Set.not_subset.1 hHle
      have hty : t * y ∈ yamadaW₃ d t := by
        have := hHK hyH
        rw [h.mem_sup_zpowers_iff_of_normalizer htW₃] at this
        exact this.resolve_left hyW
      have hHc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [show g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group, hWc a ha b hb]
        group
      have hinf : H ⊓ yamadaW₃ d t ≤ d.W.map L.subtype := fun x hx => by
        obtain ⟨hxH, hxW⟩ := Subgroup.mem_inf.1 hx
        refine hCt (Subgroup.mem_inf.2 ⟨hxW, mem_centralizer_singleton_iff.2 ?_⟩)
        have h1 := hHc x hxH y hyH
        have h2 := hWc x hxW _ hty
        have e : y = t * (t * y) := by rw [← mul_assoc, h.t_mul_t, one_mul]
        rw [e] at h1
        apply mul_right_cancel (b := t * y)
        calc x * t * (t * y) = x * (t * (t * y)) := mul_assoc _ _ _
          _ = t * (t * y) * x := h1
          _ = t * (x * (t * y)) := by rw [mul_assoc, ← h2]
          _ = t * x * (t * y) := (mul_assoc _ _ _).symm
      have hcardH : Nat.card H = (2 ^ f) ^ 10 := by
        rw [hH, Subgroup.card_map_of_injective (MulAut.conj g).injective, h521.2.2]
      have hK : Nat.card (yamadaW₃ d t ⊔ zpowers t : Subgroup G) = 2 * (2 ^ f) ^ 10 := by
        rw [h.card_sup_zpowers_of_not_mem htW₃ htW₃', h521.2.2]
      have hHN : H ≤ normalizer (yamadaW₃ d t : Set G) := hHK.trans
        (sup_le le_normalizer ((zpowers_le).2 htW₃))
      have h1 := card_sup_mul_card_inf_eq_D4 hHN
      have h2 : Nat.card (yamadaW₃ d t ⊔ H : Subgroup G) ≤ 2 * (2 ^ f) ^ 10 :=
        hK ▸ Subgroup.card_le_of_le (sup_le le_sup_left hHK)
      have h3 : Nat.card (yamadaW₃ d t ⊓ H : Subgroup G) ≤ (2 ^ f) ^ 5 := by
        rw [inf_comm]
        calc Nat.card (H ⊓ yamadaW₃ d t : Subgroup G) ≤ Nat.card (d.W.map L.subtype) :=
              Subgroup.card_le_of_le hinf
          _ = (2 ^ f) ^ 5 := by rw [Subgroup.card_subtype, d.card_W]
      rw [h521.2.2, hcardH] at h1
      have h4 : (2 ^ f) ^ 10 * (2 ^ f) ^ 10 ≤ 2 * (2 ^ f) ^ 10 * (2 ^ f) ^ 5 := by
        rw [← h1]
        exact Nat.mul_le_mul h2 h3
      have hq2 : 2 ≤ 2 ^ f := d.two_le_q
      have h5 : 2 * (2 ^ f) ^ 5 < (2 ^ f) ^ 10 := by
        calc 2 * (2 ^ f) ^ 5 < (2 ^ f) ^ 5 * (2 ^ f) ^ 5 := by
              apply Nat.mul_lt_mul_of_pos_right _ (by positivity)
              calc 2 < 2 ^ 5 := by norm_num
                _ ≤ (2 ^ f) ^ 5 := Nat.pow_le_pow_left hq2 5
          _ = (2 ^ f) ^ 10 := by ring
      have h6 : 2 * (2 ^ f) ^ 10 * (2 ^ f) ^ 5 < (2 ^ f) ^ 10 * (2 ^ f) ^ 10 := by
        calc 2 * (2 ^ f) ^ 10 * (2 ^ f) ^ 5 = (2 * (2 ^ f) ^ 5) * (2 ^ f) ^ 10 := by ring
          _ < (2 ^ f) ^ 10 * (2 ^ f) ^ 10 := Nat.mul_lt_mul_of_pos_right h5 (by positivity)
      exact absurd h4 (not_le.2 h6)
    have hgt : g * t * g⁻¹ ∈ yamadaW₃ d t ⊔ zpowers t :=
      (mem_normalizer_iff.1 hg t).1 (mem_sup_right (mem_zpowers t))
    have hgt' : t * (g * t * g⁻¹) ∈ yamadaW₃ d t := by
      rw [h.mem_sup_zpowers_iff_of_normalizer htW₃] at hgt
      refine hgt.resolve_left fun h1 => htW₃' ?_
      have := (mem_normalizer_iff.1 (inv_mem hgW₃) _).1 h1
      rwa [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
    have htt : t * (g * t * g⁻¹) ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h1 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
        rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, h.t_mul_t, mul_one,
          mul_inv_cancel]
      have h2 := hsq _ hgt'
      calc t * (g * t * g⁻¹) * t = t * (g * t * g⁻¹) * t * ((g * t * g⁻¹) * (g * t * g⁻¹)) := by
            rw [h1, mul_one]
        _ = (t * (g * t * g⁻¹) * t * (g * t * g⁻¹)) * (g * t * g⁻¹) := by group
        _ = (g * t * g⁻¹) := by
            rw [show t * (g * t * g⁻¹) * t * (g * t * g⁻¹) =
              (t * (g * t * g⁻¹)) * (t * (g * t * g⁻¹)) by group, h2, one_mul]
        _ = t * (t * (g * t * g⁻¹)) := by rw [← mul_assoc, h.t_mul_t, one_mul]
    have htW : t * (g * t * g⁻¹) ∈ d.W.map L.subtype := hCt (Subgroup.mem_inf.2 ⟨hgt', htt⟩)
    have hgW : g ∈ normalizer ((d.W.map L.subtype : Subgroup G) : Set G) :=
      mem_normalizer_fintype fun w hw => by
        have hwW₃ : g * w * g⁻¹ ∈ yamadaW₃ d t := (mem_normalizer_iff.1 hgW₃ w).1 (hWW₃ hw)
        refine hCt (Subgroup.mem_inf.2 ⟨hwW₃, mem_centralizer_singleton_iff.2 ?_⟩)
        have hwt : w * t = t * w := mem_centralizer_singleton_iff.1
          (h.L_le_centralizer (map_subtype_le _ hw))
        have h1 : (g * w * g⁻¹) * (g * t * g⁻¹) = (g * t * g⁻¹) * (g * w * g⁻¹) := by
          rw [show g * w * g⁻¹ * (g * t * g⁻¹) = g * (w * t) * g⁻¹ by group, hwt]
          group
        have h2 := hWc _ hwW₃ _ hgt'
        have e : g * t * g⁻¹ = t * (t * (g * t * g⁻¹)) := by
          rw [← mul_assoc, h.t_mul_t, one_mul]
        rw [e] at h1
        apply mul_right_cancel (b := t * (g * t * g⁻¹))
        calc g * w * g⁻¹ * t * (t * (g * t * g⁻¹)) =
            g * w * g⁻¹ * (t * (t * (g * t * g⁻¹))) := mul_assoc _ _ _
          _ = t * (t * (g * t * g⁻¹)) * (g * w * g⁻¹) := h1
          _ = t * ((g * w * g⁻¹) * (t * (g * t * g⁻¹))) := by rw [mul_assoc, ← h2]
          _ = t * (g * w * g⁻¹) * (t * (g * t * g⁻¹)) := (mul_assoc _ _ _).symm
    refine h.mem_normalizer_sup_zpowers_D3 (h.t_mem_normalizer_map_D1 d.W) hgW ?_
    have e : g * t * g⁻¹ = t * (t * (g * t * g⁻¹)) := by rw [← mul_assoc, h.t_mul_t, one_mul]
    rw [e]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left htW)
  ·
    have hgL₂ : g ∈ normalizer (yamadaL₂ d t : Set G) := by
      rw [h5171.1]
      exact hg
    have hgW₃ : g ∈ normalizer (yamadaW₃ d t : Set G) :=
      mem_normalizer_inf_D4 (normalizer_yamadaL₂_le_normalizer_yamadaL₃ d hgL₂)
        (mem_normalizer_centralizer_D4 ((h.normalizer_yamadaV₂_le d h562 h592).1
          (h.normalizer_yamadaL₂_le d h591 h592 hgL₂)))
    refine h.mem_normalizer_sup_zpowers_D3 htW₃ hgW₃ ?_
    have := (mem_normalizer_iff.1 hg t).1 (mem_sup_right (mem_zpowers t))
    exact (sup_le_sup_right hWW₃ _) this

end Normalizer

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
