module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL3Five
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Ten
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Nine

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem yamadaF₄_le_yamadaS₄ {q : ℕ} (d : TrialityD4Data L q) :
    yamadaF₄ d t ≤ yamadaS₄ d t := fun x hx =>
  Subgroup.mem_inf.2 ⟨(inf_le_left : yamadaM₄ d t ≤ yamadaR₄ d t) (yamadaF₄_le_yamadaM₄ d t hx),
    (inf_le_right : yamadaD₅ d t ≤ centralizer (yamadaV₁ d t : Set G))
      ((inf_le_right : yamadaD₄ d t ≤ yamadaD₅ d t) (yamadaF₄_le_yamadaD₄ d t hx))⟩

theorem t_mem_normalizer_yamadaF₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∈ normalizer (yamadaF₄ d t : Set G) := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have htR₄ : t ∈ yamadaR₄ d t := h.t_mem_yamadaR₄ d hNH h561 h562 h591 h592 h593
  have htM₄ : t ∈ normalizer (yamadaM₄ d t : Set G) :=
    Common.mem_normalizer_inf (le_normalizer htR₄)
      (mem_normalizer_centralizer_C8 (h.t_mem_normalizer_yamadaY₂ d))
  have htC₅ : t ∈ normalizer (yamadaC₅ d t : Set G) :=
    le_normalizer (yamadaC₁_le_yamadaC₅ d t (h.t_mem_yamadaC₁ d))
  have htV₁ : t ∈ normalizer (centralizer (yamadaV₁ d t : Set G) : Set G) :=
    mem_normalizer_centralizer_C8
      (normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (h.t_mem_normalizer_yamadaD₁ d))
  have htD₄ : t ∈ normalizer (yamadaD₄ d t : Set G) :=
    Common.mem_normalizer_inf (le_normalizer htR₄) (Common.mem_normalizer_inf htC₅ htV₁)
  exact Common.mem_normalizer_inf htM₄ htD₄

theorem yamadaR₄_inf_centralizer_le (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaR₄ d t ⊓ centralizer ({t} : Set G) ≤ d.S.map L.subtype ⊔ zpowers t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h514 := h.yamada_5_14 d hNH h561 h562 h591 h592 h593
  have h512 := h.yamada_5_12 d hNH h561 h562 h591 h592 h593
  have hR₄R₅ : yamadaR₄ d t ≤ yamadaR₅ d t := h514.2.2.2.2.2.1
  have hSC₅ : d.S.map L.subtype ≤ normalizer (yamadaC₅ d t : Set G) :=
    (h.S_le_normalizer_yamadaC₁ d).trans (le_normalizer_yamadaC₅ d t)
  have hC₅C : yamadaC₅ d t ⊓ centralizer ({t} : Set G) = d.D.map L.subtype ⊔ zpowers t :=
    h512.1.2.2.2
  have hDS : d.D.map L.subtype ⊔ zpowers t ≤ d.S.map L.subtype ⊔ zpowers t :=
    sup_le ((map_mono (f := L.subtype) d.D_le_S).trans le_sup_left) le_sup_right
  intro x hx
  obtain ⟨hxR₄, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxR₅ : x ∈ ((yamadaC₅ d t ⊔ d.S.map L.subtype : Subgroup G) : Set G) := hR₄R₅ hxR₄
  rw [coe_mul_of_right_le_normalizer_left _ _ hSC₅] at hxR₅
  obtain ⟨c, hc, s, hs, hcs⟩ := Set.mem_mul.1 hxR₅
  have hsC : s ∈ centralizer ({t} : Set G) := h.L_le_centralizer (map_subtype_le _ hs)
  have hcC : c ∈ centralizer ({t} : Set G) := by
    have hc' : c = x * s⁻¹ := by rw [← hcs]; group
    rw [hc']
    exact mul_mem hxC (inv_mem hsC)
  have hcD : c ∈ d.D.map L.subtype ⊔ zpowers t := by
    rw [← hC₅C]
    exact Subgroup.mem_inf.2 ⟨hc, hcC⟩
  rw [← hcs]
  exact mul_mem (hDS hcD) (mem_sup_left hs)

theorem normalizer_yamadaR₄_inf_centralizer_le (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    normalizer (yamadaR₄ d t : Set G) ⊓ centralizer ({t} : Set G) ≤
      centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have h514 := h.yamada_5_14 d hNH h561 h562 h591 h592 h593
  have h5172 := h.yamada_5_17_2 d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hS₃ : d.S.map L.subtype ≤ yamadaR₃ d t := by
    rw [h5172.2]
    exact le_sup_right
  have hS₄ : d.S.map L.subtype ≤ yamadaR₄ d t := hS₃.trans h514.2.2.2.2.1.1
  have hSC : d.S.map L.subtype ≤ centralizer ({t} : Set G) := fun s hs =>
    h.L_le_centralizer (map_subtype_le _ hs)
  have htS : t ∈ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) :=
    h.t_mem_normalizer_map d.S
  intro c hc
  obtain ⟨hcN, hcC⟩ := Subgroup.mem_inf.1 hc
  refine Subgroup.mem_inf.2 ⟨hcC, ?_⟩
  have hcL : c ∈ normalizer (L : Set G) := h.centralizer_le_normalizer hcC
  apply mem_normalizer_fintype
  intro x hx
  have hxL : x ∈ L := map_subtype_le _ hx
  have hcxR₄ : c * x * c⁻¹ ∈ yamadaR₄ d t := (mem_normalizer_iff.1 hcN x).1 (hS₄ hx)
  have hcxC : c * x * c⁻¹ ∈ centralizer ({t} : Set G) :=
    mul_mem (mul_mem hcC (hSC hx)) (inv_mem hcC)
  have hcxL : c * x * c⁻¹ ∈ L := (mem_normalizer_iff.1 hcL x).1 hxL
  have hmem := h.yamadaR₄_inf_centralizer_le d hlay (Subgroup.mem_inf.2 ⟨hcxR₄, hcxC⟩)
  rcases (h.mem_sup_zpowers_iff_of_normalizer htS).1 hmem with h1 | h1
  · exact h1
  · exfalso
    apply h.t_not_mem_L
    have h2 : t * (c * x * c⁻¹) * (c * x * c⁻¹)⁻¹ ∈ L :=
      mul_mem (map_subtype_le _ h1) (inv_mem hcxL)
    rwa [mul_inv_cancel_right] at h2

theorem mul_self_mem_yamadaW₃_of_mem_yamadaF₄ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {x : G}
    (hx : x ∈ yamadaF₄ d t) : x * x ∈ yamadaW₃ d t := by
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
  have hD₅ : x ∈ yamadaD₅ d t :=
    (inf_le_right : yamadaD₄ d t ≤ yamadaD₅ d t) (yamadaF₄_le_yamadaD₄ d t hx)
  have hV₁ : x * x ∈ yamadaV₁ d t :=
    h.mul_self_mem_yamadaV₁_of_mem_yamadaD₅ d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e
      h520 h5221 h521 hD₅
  exact h.yamadaV₁_le_yamadaW₃_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102 hV₁

theorem exists_mul_of_mem_normalizer_yamadaW₃ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {x : G}
    (hx : x ∈ normalizer ((yamadaW₃ d t ⊔ zpowers t : Subgroup G) : Set G)) :
    ∃ l ∈ yamadaL₃ d t, ∃ c ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.Y.map L.subtype : Subgroup G) : Set G), l * c = x := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have h5171 := h.yamada_5_17_1 d hNH h561 h562 h591 h592 h593 h5101 h5102
  have h522 := h.yamada_5_22_2 d hlay
  have hNCY₂ : centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaL₂ d t : Set G) := by
    rw [h5171.2.1]
    exact le_sup_right
  have hNCY₃ : centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaL₃ d t : Set G) :=
    hNCY₂.trans (normalizer_yamadaL₂_le_normalizer_yamadaL₃ d)
  rw [h522] at hx
  have hset := coe_mul_of_right_le_normalizer_left (yamadaL₃ d t)
    (centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G)) hNCY₃
  have hxmem : x ∈ ((yamadaL₃ d t ⊔ (centralizer ({t} : Set G) ⊓
      normalizer ((d.Y.map L.subtype : Subgroup G) : Set G)) : Subgroup G) : Set G) := hx
  rw [hset] at hxmem
  exact Set.mem_mul.1 hxmem

theorem yamadaF₄_inf_normalizer_yamadaW₃_le (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaF₄ d t ⊓ normalizer ((yamadaW₃ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      yamadaF₃ d t := by
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
  have h5221 := h.yamada_5_22_1 d hlay
  have h514 := h.yamada_5_14 d hNH h561 h562 h591 h592 h593
  have h524 := h.yamada_5_24 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221
  have h5172 := h.yamada_5_17_2 d hNH h561 h562 h591 h592 h593 h5101 h5102
  obtain ⟨⟨hL₄eq, -⟩, ⟨-, hL₄R₃, -, -⟩, -⟩ := h524
  have htL₃ : t ∈ yamadaL₃ d t := by
    rw [h.yamadaL₃_eq_sup d hlay]
    exact mem_sup_right (mem_zpowers t)
  have hL₃R₃ : yamadaL₃ d t ≤ yamadaR₃ d t := h.yamadaL₃_le_yamadaR₃_D3 d hlay
  have hR₃R₄ : yamadaR₃ d t ≤ yamadaR₄ d t := h514.2.2.2.2.1.1
  have hL₃R₄ : yamadaL₃ d t ≤ yamadaR₄ d t := hL₃R₃.trans hR₃R₄
  have hSR₃ : d.S.map L.subtype ≤ yamadaR₃ d t := by
    rw [h5172.2]
    exact le_sup_right
  intro x hx
  obtain ⟨hxF₄, hxN⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨l, hl, c, hc, hlc⟩ := exists_mul_of_mem_normalizer_yamadaW₃ h d hlay hxN
  have hxM₄ : x ∈ yamadaM₄ d t := yamadaF₄_le_yamadaM₄ d t hxF₄
  have hxR₄ : x ∈ yamadaR₄ d t := (inf_le_left : yamadaM₄ d t ≤ yamadaR₄ d t) hxM₄
  have hxD₅ : x ∈ yamadaD₅ d t :=
    (inf_le_right : yamadaD₄ d t ≤ yamadaD₅ d t) (yamadaF₄_le_yamadaD₄ d t hxF₄)
  have hcC : c ∈ centralizer ({t} : Set G) := (Subgroup.mem_inf.1 hc).1
  have hcR₄ : c ∈ yamadaR₄ d t := by
    have hc' : c = l⁻¹ * x := by rw [← hlc]; group
    rw [hc']
    exact mul_mem (inv_mem (hL₃R₄ hl)) hxR₄
  have hcR₃ : c ∈ yamadaR₃ d t := by
    have hcS := h.yamadaR₄_inf_centralizer_le d hlay (Subgroup.mem_inf.2 ⟨hcR₄, hcC⟩)
    have hS₃t : d.S.map L.subtype ⊔ zpowers t ≤ yamadaR₃ d t :=
      sup_le hSR₃ ((zpowers_le).2 (hL₃R₃ htL₃))
    exact hS₃t hcS
  have hxR₃ : x ∈ yamadaR₃ d t := by
    rw [← hlc]
    exact mul_mem (hL₃R₃ hl) hcR₃
  have hxL₄ : x ∈ yamadaL₄ d t := by
    rw [hL₄eq]
    exact mem_sup_left hxM₄
  have hxL₃ : x ∈ yamadaL₃ d t := by
    rw [← hL₄R₃]
    exact Subgroup.mem_inf.2 ⟨hxL₄, hxR₃⟩
  have hM₄C : yamadaM₄ d t ≤ centralizer (yamadaY₂ d t : Set G) := inf_le_right
  have hxM₃ : x ∈ yamadaM₃ d t := Subgroup.mem_inf.2 ⟨hxL₃, hM₄C hxM₄⟩
  have hD₅V : yamadaD₅ d t ≤ centralizer (yamadaV₁ d t : Set G) := inf_le_right
  have hxS₃ : x ∈ yamadaS₃ d t := Subgroup.mem_inf.2 ⟨hxR₃, hD₅V hxD₅⟩
  have hD₅C₅ : yamadaD₅ d t ≤ yamadaC₅ d t := inf_le_left
  have hxD₃ : x ∈ yamadaD₃ d t := Subgroup.mem_inf.2 ⟨hxS₃, hD₅C₅ hxD₅⟩
  exact Subgroup.mem_inf.2 ⟨hxM₃, hxD₃⟩

theorem normalizer_yamadaR₄_inf_le (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hK : normalizer (yamadaR₄ d t : Set G) ≤
      normalizer (yamadaS₄ d t : Set G) ⊓ normalizer (yamadaW₃ d t : Set G))
    (hL₄ : ∀ a ∈ yamadaF₃ d t, ∃ r ∈ yamadaL₄ d t, ∃ w ∈ yamadaW₃ d t,
      r * t * r⁻¹ = t * a * w) :
    normalizer (yamadaR₄ d t : Set G) ⊓
        normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      yamadaR₄ d t ⊔ (centralizer ({t} : Set G) ⊓
        normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) := by
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
  have h5221 := h.yamada_5_22_1 d hlay
  have h514 := h.yamada_5_14 d hNH h561 h562 h591 h592 h593
  have h524 := h.yamada_5_24 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221
  obtain ⟨-, ⟨hR₄eq, -, -, -⟩, -⟩ := h524
  have hL₄R₄ : yamadaL₄ d t ≤ yamadaR₄ d t := by
    rw [hR₄eq]
    exact le_sup_left
  have hF₄R₄ : yamadaF₄ d t ≤ yamadaR₄ d t :=
    (yamadaF₄_le_yamadaM₄ d t).trans (inf_le_left : yamadaM₄ d t ≤ yamadaR₄ d t)
  have hF₄S₄ : yamadaF₄ d t ≤ yamadaS₄ d t := yamadaF₄_le_yamadaS₄ d
  have hR₃R₄ : yamadaR₃ d t ≤ yamadaR₄ d t := h514.2.2.2.2.1.1
  have hL₃R₃ : yamadaL₃ d t ≤ yamadaR₃ d t := h.yamadaL₃_le_yamadaR₃_D3 d hlay
  have hL₃R₄ : yamadaL₃ d t ≤ yamadaR₄ d t := hL₃R₃.trans hR₃R₄
  have htF₄ : t ∈ normalizer (yamadaF₄ d t : Set G) := h.t_mem_normalizer_yamadaF₄ d hlay
  have htL₃ : t ∈ yamadaL₃ d t := by
    rw [h.yamadaL₃_eq_sup d hlay]
    exact mem_sup_right (mem_zpowers t)
  have htW₃ : t ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaL₃_le_normalizer_yamadaW₃ d hlay htL₃
  intro g hg
  obtain ⟨hgR, hgF⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨hgS₄, hgW₃⟩ := Subgroup.mem_inf.1 (hK hgR)
  have hgt : g * t * g⁻¹ ∈ yamadaF₄ d t ⊔ zpowers t :=
    (mem_normalizer_iff.1 hgF t).1 (mem_sup_right (mem_zpowers t))
  obtain ⟨a, haF₄, hgtg⟩ : ∃ a ∈ yamadaF₄ d t, g * t * g⁻¹ = t * a := by
    rcases (h.mem_sup_zpowers_iff_of_normalizer htF₄).1 hgt with h1 | h1
    · exfalso
      have h2 : g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ ∈ yamadaS₄ d t :=
        (mem_normalizer_iff.1 (inv_mem hgS₄) _).1 (hF₄S₄ h1)
      rw [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at h2
      exact h.t_not_mem_centralizer_yamadaV₁ d hlay (Subgroup.mem_inf.1 h2).2
    · refine ⟨t * (g * t * g⁻¹), h1, ?_⟩
      calc g * t * g⁻¹ = (t * t) * (g * t * g⁻¹) := by rw [h.t_mul_t, one_mul]
        _ = t * (t * (g * t * g⁻¹)) := mul_assoc _ _ _
  have hsq : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, h.t_mul_t, mul_one,
      mul_inv_cancel]
  rw [hgtg] at hsq
  have hta2 : t * a * t * a = 1 := by simpa only [mul_assoc] using hsq
  have hta : t * a * t = a⁻¹ := eq_inv_of_mul_eq_one_left hta2
  have haR₄ : a ∈ yamadaR₄ d t := hF₄R₄ haF₄
  have haN : a ∈ normalizer (yamadaW₃ d t : Set G) :=
    (Subgroup.mem_inf.1 (hK (le_normalizer haR₄))).2
  have hκ : a⁻¹ * a⁻¹ ∈ yamadaW₃ d t :=
    h.mul_self_mem_yamadaW₃_of_mem_yamadaF₄ d hlay (inv_mem haF₄)
  have hat_eq : a * t * a⁻¹ = t * (a⁻¹ * a⁻¹) := by
    calc a * t * a⁻¹ = (t * t) * (a * t * a⁻¹) := by rw [h.t_mul_t, one_mul]
      _ = t * (t * a * t) * a⁻¹ := by group
      _ = t * a⁻¹ * a⁻¹ := by rw [hta]
      _ = t * (a⁻¹ * a⁻¹) := mul_assoc _ _ _
  have hat : a * t * a⁻¹ ∈ yamadaW₃ d t ⊔ zpowers t := by
    rw [hat_eq]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hκ)
  have haF₃ : a ∈ yamadaF₃ d t :=
    h.yamadaF₄_inf_normalizer_yamadaW₃_le d hlay
      (Subgroup.mem_inf.2 ⟨haF₄, h.mem_normalizer_sup_zpowers_D3 htW₃ haN hat⟩)
  obtain ⟨r, hrL₄, w, hwW₃, hrw⟩ := hL₄ a haF₃
  have hrR₄ : r ∈ yamadaR₄ d t := hL₄R₄ hrL₄
  have hrN : r ∈ normalizer (yamadaW₃ d t : Set G) :=
    (Subgroup.mem_inf.1 (hK (le_normalizer hrR₄))).2
  have hta' : t * a = r * t * r⁻¹ * w⁻¹ := by
    rw [hrw]
    group
  have hkey : r⁻¹ * g * t * (r⁻¹ * g)⁻¹ = t * (r⁻¹ * w⁻¹ * r) := by
    calc r⁻¹ * g * t * (r⁻¹ * g)⁻¹ = r⁻¹ * (g * t * g⁻¹) * r := by group
      _ = r⁻¹ * (t * a) * r := by rw [hgtg]
      _ = r⁻¹ * (r * t * r⁻¹ * w⁻¹) * r := by rw [hta']
      _ = t * (r⁻¹ * w⁻¹ * r) := by group
  have hw' : r⁻¹ * w⁻¹ * r ∈ yamadaW₃ d t := by
    have h3 := (mem_normalizer_iff.1 (inv_mem hrN) w⁻¹).1 (inv_mem hwW₃)
    rwa [inv_inv] at h3
  have hxt : r⁻¹ * g * t * (r⁻¹ * g)⁻¹ ∈ yamadaW₃ d t ⊔ zpowers t := by
    rw [hkey]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hw')
  have hxN : r⁻¹ * g ∈ normalizer ((yamadaW₃ d t ⊔ zpowers t : Subgroup G) : Set G) :=
    h.mem_normalizer_sup_zpowers_D3 htW₃ (mul_mem (inv_mem hrN) hgW₃) hxt
  obtain ⟨l, hl, c, hc, hlc⟩ := exists_mul_of_mem_normalizer_yamadaW₃ h d hlay hxN
  have hlR₄ : l ∈ yamadaR₄ d t := hL₃R₄ hl
  have hcC : c ∈ centralizer ({t} : Set G) := (Subgroup.mem_inf.1 hc).1
  have hcN : c ∈ normalizer (yamadaR₄ d t : Set G) := by
    have hc' : c = l⁻¹ * (r⁻¹ * g) := by rw [← hlc]; group
    rw [hc']
    exact mul_mem (inv_mem (le_normalizer hlR₄)) (mul_mem (inv_mem (le_normalizer hrR₄)) hgR)
  have hcNCS := h.normalizer_yamadaR₄_inf_centralizer_le d hlay
    (Subgroup.mem_inf.2 ⟨hcN, hcC⟩)
  have hg_eq : g = r * l * c := by
    rw [mul_assoc, hlc]
    group
  rw [hg_eq]
  exact mul_mem (mem_sup_left (mul_mem hrR₄ hlR₄)) (mem_sup_right hcNCS)

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
