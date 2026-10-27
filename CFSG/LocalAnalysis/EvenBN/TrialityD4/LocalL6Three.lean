module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL6
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalR4
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalR4Frattini

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

section NCS

theorem centralizer_inf_normalizer_S_le_normalizer_yamadaR₅ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) :
    centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaR₅ d t : Set G) := fun _ hc =>
  Common.mem_normalizer_sup (le_normalizer_yamadaC₅ d t (le_normalizer_yamadaC₁ d t
    (h.normalizer_yamadaR_le_tV d (h.centralizer_inf_normalizer_S_le d hc)))) hc.2

theorem centralizer_inf_normalizer_S_le_normalizer_yamadaR₄ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaR₄ d t : Set G) := fun c hc => by
  have hy := h.l6Hyps d hlay
  have hcR := h.centralizer_inf_normalizer_S_le d hc
  have hcD₁ : c ∈ normalizer (yamadaD₁ d t : Set G) :=
    hy.hNH.1 (le_normalizer_yamadaC₁ d t (h.normalizer_yamadaR_le_tV d hcR))
  have hcL₂ : c ∈ normalizer (yamadaL₂ d t : Set G) :=
    le_normalizer_yamadaL₂ d t (h.normalizer_yamadaR_le_tY d hcR)
  have hcF₁ : c ∈ normalizer (yamadaF₁ d t : Set G) :=
    Common.mem_normalizer_inf (Common.mem_normalizer_inf hcL₂
      (Common.mem_normalizer_sup hc.2 hcD₁)) hcD₁
  have hcF₁t : c ∈ normalizer ((yamadaF₁ d t ⊔ zpowers t : Subgroup G) : Set G) :=
    Common.mem_normalizer_sup hcF₁
      (mem_normalizer_zpowers_of_comm_D4 (mem_centralizer_singleton_iff.1 hc.1))
  exact Common.mem_normalizer_inf (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₅ d hc)
    (le_normalizer hcF₁t)

theorem centralizer_inf_normalizer_S_le_normalizer_yamadaR₃ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaR₃ d t : Set G) := fun c hc => by
  have hy := h.l6Hyps d hlay
  have hcR := h.centralizer_inf_normalizer_S_le d hc
  have hcV₂ : c ∈ normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) :=
    (normalizer_yamadaR₂_le d hy.h592 hy.h5101 hy.h5102
      (h.normalizer_yamadaR_le_normalizer_yamadaR₂ d hcR)).1
  have hcW : c ∈ normalizer ((d.W.map L.subtype : Subgroup G) : Set G) :=
    (h.normalizer_yamadaV₂_le d hy.h562 hy.h592).2.2 hcV₂
  have hcV₁ : c ∈ normalizer (yamadaV₁ d t : Set G) :=
    normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t
      (hy.hNH.1 (le_normalizer_yamadaC₁ d t (h.normalizer_yamadaR_le_tV d hcR)))
  have hcW₁t : c ∈ normalizer ((yamadaW₁ d t ⊔ zpowers t : Subgroup G) : Set G) :=
    Common.mem_normalizer_sup (Common.mem_normalizer_sup hcW hcV₁)
      (mem_normalizer_zpowers_of_comm_D4 (mem_centralizer_singleton_iff.1 hc.1))
  exact Common.mem_normalizer_inf (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₅ d hc)
    (le_normalizer hcW₁t)

theorem centralizer_inf_normalizer_S_le_normalizer_yamadaL₆ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaL₆ d t : Set G) := fun c hc =>
  le_normalizer_yamadaL₆ d t (h.centralizer_inf_normalizer_Y_le_H d hlay ⟨hc.1,
    h.normalizer_tY_le_normalizer_Y d
      (h.normalizer_yamadaR_le_tY d (h.centralizer_inf_normalizer_S_le d hc))⟩)

theorem centralizer_inf_normalizer_S_le_normalizer_yamadaR₆ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaR₆ d t : Set G) := fun _ hc =>
  Common.mem_normalizer_sup (h.centralizer_inf_normalizer_S_le_normalizer_yamadaL₆ d hlay hc) hc.2

theorem S_map_le_centralizer_inf_normalizer_L6T (h : Setup G L f t) {q : ℕ}
    (d : TrialityD4Data L q) :
    d.S.map L.subtype ≤ centralizer ({t} : Set G) ⊓
      normalizer ((d.S.map L.subtype : Subgroup G) : Set G) := fun _ hs =>
  ⟨h.S_le_centralizer d hs, le_normalizer hs⟩

end NCS

section Six

theorem conj_inv_t_eq_L6T {y m : G} (hym : y * t * y⁻¹ = t * m) :
    y⁻¹ * t * y = t * (y⁻¹ * m⁻¹ * y) := by
  have h1 : y⁻¹ * t * y * (y⁻¹ * m * y) = t := by
    calc y⁻¹ * t * y * (y⁻¹ * m * y) = y⁻¹ * (t * m) * y := by group
      _ = y⁻¹ * (y * t * y⁻¹) * y := by rw [hym]
      _ = t := by group
  rw [eq_mul_inv_of_mul_eq h1]
  group

theorem t_mem_yamadaL₃_L6T (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∈ yamadaL₃ d t := by
  rw [h.yamadaL₃_eq_sup d hlay]
  exact mem_sup_right (mem_zpowers t)

theorem yamadaL₆_le_normalizer_yamadaF₃_L6T (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaL₆ d t ≤ normalizer (yamadaF₃ d t : Set G) := by
  intro y hy
  refine mem_normalizer_fintype fun a ha => ?_
  have hw : y * a * y⁻¹ * a⁻¹ ∈ yamadaW₃ d t :=
    h.commutator_mem_yamadaW₃_of_mem_yamadaT₆ d hlay (h.yamadaL₆_le_yamadaT₆ d hlay hy)
      (mem_inf.1 ha).1
  have := mul_mem (h.yamadaW₃_le_yamadaF₃ d hlay hw) ha
  rwa [inv_mul_cancel_right] at this

theorem commutator_mem_yamadaF₃_L6T (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {n s : G} (hn : n ∈ yamadaL₃ d t) (hs : s ∈ d.S.map L.subtype) :
    n * s * n⁻¹ * s⁻¹ ∈ yamadaF₃ d t := by
  have hy := h.l6Hyps d hlay
  have hnR₅ : n ∈ yamadaR₅ d t := (mem_inf.1 (h.yamadaL₃_le_yamadaR₃_D3 d hlay hn)).1
  have hsR₅ : s ∈ yamadaR₅ d t := mem_sup_right hs
  have hD₅ : n * s * n⁻¹ * s⁻¹ ∈ yamadaD₅ d t := by
    have h1 := h.commutator_yamadaR₅_le_yamadaD₅ d hy.h561 hy.h593 hy.h520
      (commutator_mem_commutator hnR₅ hsR₅)
    rwa [commutatorElement_def] at h1
  have hL₃ : n * s * n⁻¹ * s⁻¹ ∈ yamadaL₃ d t := by
    have := mul_mem hn ((mem_normalizer_iff.1 (h.S_le_normalizer_yamadaL₃ d hs) n⁻¹).1
      (inv_mem hn))
    rwa [← mul_assoc, ← mul_assoc] at this
  exact h.yamadaL₃_inf_yamadaD₅_le d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101
    hy.h5102 hy.h520 (mem_inf.2 ⟨hL₃, hD₅⟩)

theorem mem_yamadaL₄_of_mem_yamadaL₆_L6T (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x a : G} (hx : x ∈ yamadaL₆ d t) (ha : a ∈ yamadaF₃ d t)
    (hxt : x * t * x⁻¹ = t * a) : x ∈ yamadaL₄ d t := by
  obtain ⟨r, hrL₄, w, hwW₃, hrw⟩ := h.exists_mem_yamadaL₄_conj_eq d hlay ha
  have hrL₆ : r ∈ yamadaL₆ d t :=
    h.yamadaT₆_le_yamadaL₆ d hlay (h.yamadaL₄_le_yamadaT₆ d hlay hrL₄)
  have hrN : r ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaR₄_le_normalizer_yamadaW₃_R4 d hlay (mem_inf.1 hrL₄).1
  have hxN : x ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.normalizer_yamadaL₃_le_normalizer_yamadaW₃ d hlay (yamadaL₆_le d t hx).1
  have htW₃ : t ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaL₃_le_normalizer_yamadaW₃ d hlay (h.t_mem_yamadaL₃_L6T d hlay)
  have hta' : t * a = r * t * r⁻¹ * w⁻¹ := by
    rw [hrw]
    group
  have hkey : r⁻¹ * x * t * (r⁻¹ * x)⁻¹ = t * (r⁻¹ * w⁻¹ * r) := by
    calc r⁻¹ * x * t * (r⁻¹ * x)⁻¹ = r⁻¹ * (x * t * x⁻¹) * r := by group
      _ = r⁻¹ * (t * a) * r := by rw [hxt]
      _ = r⁻¹ * (r * t * r⁻¹ * w⁻¹) * r := by rw [hta']
      _ = t * (r⁻¹ * w⁻¹ * r) := by group
  have hw' : r⁻¹ * w⁻¹ * r ∈ yamadaW₃ d t := by
    have h3 := (mem_normalizer_iff.1 (inv_mem hrN) w⁻¹).1 (inv_mem hwW₃)
    rwa [inv_inv] at h3
  have hut : r⁻¹ * x * t * (r⁻¹ * x)⁻¹ ∈ yamadaW₃ d t ⊔ zpowers t := by
    rw [hkey]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hw')
  have huN : r⁻¹ * x ∈ normalizer ((yamadaW₃ d t ⊔ zpowers t : Subgroup G) : Set G) :=
    h.mem_normalizer_sup_zpowers_D3 htW₃ (mul_mem (inv_mem hrN) hxN) hut
  have huL₃ : r⁻¹ * x ∈ yamadaL₃ d t := by
    rw [← h.yamadaL₆_inf_normalizer d hlay]
    exact mem_inf.2 ⟨mul_mem (inv_mem hrL₆) hx, huN⟩
  have := mul_mem hrL₄ (h.yamadaL₃_le_yamadaL₄ d hlay huL₃)
  rwa [mul_inv_cancel_left] at this

theorem commutator_mem_yamadaL₄_of_mem_yamadaL₆_L6T (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {y s : G} (hy : y ∈ yamadaL₆ d t)
    (hs : s ∈ d.S.map L.subtype) : y * s * y⁻¹ * s⁻¹ ∈ yamadaL₄ d t := by
  have hsN₆ : s ∈ normalizer (yamadaL₆ d t : Set G) :=
    h.centralizer_inf_normalizer_S_le_normalizer_yamadaL₆ d hlay
      (h.S_map_le_centralizer_inf_normalizer_L6T d hs)
  have hst : s * t = t * s := mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)
  have hz₆ : y * s * y⁻¹ * s⁻¹ ∈ yamadaL₆ d t := by
    have := mul_mem hy ((mem_normalizer_iff.1 hsN₆ y⁻¹).1 (inv_mem hy))
    rwa [← mul_assoc, ← mul_assoc] at this
  obtain ⟨m, hm, hym⟩ := h.conj_t_mem_of_mem_yamadaL₆ d hlay hy
  have hyM₃ : y ∈ normalizer (yamadaM₃ d t : Set G) := (yamadaL₆_le d t hy).2
  have hn : y⁻¹ * m * y ∈ yamadaM₃ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hyM₃) m).1 hm
    rwa [inv_inv] at this
  have hF : y * (y⁻¹ * m * y * s * (y⁻¹ * m * y)⁻¹ * s⁻¹) * y⁻¹ ∈ yamadaF₃ d t :=
    (mem_normalizer_iff.1 (h.yamadaL₆_le_normalizer_yamadaF₃_L6T d hlay hy) _).1
      (h.commutator_mem_yamadaF₃_L6T d hlay (mem_inf.1 hn).1 hs)
  refine h.mem_yamadaL₄_of_mem_yamadaL₆_L6T d hlay hz₆ hF ?_
  have hst' : s⁻¹ * t * s = t := by rw [mul_assoc, ← hst, inv_mul_cancel_left]
  calc y * s * y⁻¹ * s⁻¹ * t * (y * s * y⁻¹ * s⁻¹)⁻¹
      = y * s * y⁻¹ * (s⁻¹ * t * s) * y * s⁻¹ * y⁻¹ := by group
    _ = y * s * (y⁻¹ * t * y) * s⁻¹ * y⁻¹ := by rw [hst']; group
    _ = y * s * (t * (y⁻¹ * m⁻¹ * y)) * s⁻¹ * y⁻¹ := by rw [conj_inv_t_eq_L6T hym]
    _ = y * (s * t) * (y⁻¹ * m⁻¹ * y) * s⁻¹ * y⁻¹ := by group
    _ = y * (t * s) * (y⁻¹ * m⁻¹ * y) * s⁻¹ * y⁻¹ := by rw [hst]
    _ = (y * t * y⁻¹) * (y * s * y⁻¹ * m⁻¹ * y * s⁻¹ * y⁻¹) := by group
    _ = t * m * (y * s * y⁻¹ * m⁻¹ * y * s⁻¹ * y⁻¹) := by rw [hym]
    _ = t * (y * (y⁻¹ * m * y * s * (y⁻¹ * m * y)⁻¹ * s⁻¹) * y⁻¹) := by group

theorem conj_mem_yamadaL₄_of_mem_yamadaL₆_L6T (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {y x : G} (hy : y ∈ yamadaL₆ d t) (hx : x ∈ yamadaL₄ d t) :
    y * x * y⁻¹ ∈ yamadaL₄ d t := by
  have hxL₆ : x ∈ yamadaL₆ d t :=
    h.yamadaT₆_le_yamadaL₆ d hlay (h.yamadaL₄_le_yamadaT₆ d hlay hx)
  have hu₆ : y * x * y⁻¹ ∈ yamadaL₆ d t := by
    have hyN : y ∈ normalizer (yamadaL₆ d t : Set G) := le_normalizer hy
    exact (mem_normalizer_iff.1 hyN x).1 hxL₆
  obtain ⟨a, ha, hxa⟩ := h.exists_conj_t_eq_mul_of_mem_yamadaL₄ d hlay hx
  obtain ⟨m, hm, hym⟩ := h.conj_t_mem_of_mem_yamadaL₆ d hlay hy
  have hmN : m ∈ normalizer (yamadaF₃ d t : Set G) :=
    h.yamadaM₃_le_normalizer_yamadaF₃ d hlay hm
  have hmW : m ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaL₃_le_normalizer_yamadaW₃ d hlay (mem_inf.1 hm).1
  have hb : y * a * y⁻¹ ∈ yamadaF₃ d t :=
    (mem_normalizer_iff.1 (h.yamadaL₆_le_normalizer_yamadaF₃_L6T d hlay hy) a).1 ha
  have hw : (y * x * y⁻¹) * m⁻¹ * (y * x * y⁻¹)⁻¹ * m ∈ yamadaW₃ d t := by
    have := h.commutator_mem_yamadaW₃_of_mem_yamadaT₆ d hlay
      (h.yamadaL₆_le_yamadaT₆ d hlay hu₆) (inv_mem hm)
    rwa [inv_inv] at this
  have hF : m * (y * a * y⁻¹) * ((y * x * y⁻¹) * m⁻¹ * (y * x * y⁻¹)⁻¹) ∈ yamadaF₃ d t := by
    have h1 : m * (y * a * y⁻¹) * m⁻¹ ∈ yamadaF₃ d t := (mem_normalizer_iff.1 hmN _).1 hb
    have h2 : m * ((y * x * y⁻¹) * m⁻¹ * (y * x * y⁻¹)⁻¹ * m) * m⁻¹ ∈ yamadaW₃ d t :=
      (mem_normalizer_iff.1 hmW _).1 hw
    have := mul_mem h1 (h.yamadaW₃_le_yamadaF₃ d hlay h2)
    rwa [show m * (y * a * y⁻¹) * m⁻¹ * (m * ((y * x * y⁻¹) * m⁻¹ * (y * x * y⁻¹)⁻¹ * m) * m⁻¹)
      = m * (y * a * y⁻¹) * ((y * x * y⁻¹) * m⁻¹ * (y * x * y⁻¹)⁻¹) by group] at this
  refine h.mem_yamadaL₄_of_mem_yamadaL₆_L6T d hlay hu₆ hF ?_
  calc (y * x * y⁻¹) * t * (y * x * y⁻¹)⁻¹ = y * x * (y⁻¹ * t * y) * x⁻¹ * y⁻¹ := by group
    _ = y * x * (t * (y⁻¹ * m⁻¹ * y)) * x⁻¹ * y⁻¹ := by rw [conj_inv_t_eq_L6T hym]
    _ = y * (x * t * x⁻¹) * (x * (y⁻¹ * m⁻¹ * y) * x⁻¹) * y⁻¹ := by group
    _ = y * (t * a) * (x * (y⁻¹ * m⁻¹ * y) * x⁻¹) * y⁻¹ := by rw [hxa]
    _ = (y * t * y⁻¹) * (y * a * y⁻¹) * ((y * x * y⁻¹) * m⁻¹ * (y * x * y⁻¹)⁻¹) := by group
    _ = t * m * (y * a * y⁻¹) * ((y * x * y⁻¹) * m⁻¹ * (y * x * y⁻¹)⁻¹) := by rw [hym]
    _ = t * (m * (y * a * y⁻¹) * ((y * x * y⁻¹) * m⁻¹ * (y * x * y⁻¹)⁻¹)) := by group

theorem yamadaR₄_eq_sup_yamadaL₄_L6T (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaR₄ d t = yamadaL₄ d t ⊔ d.S.map L.subtype := by
  have hy := h.l6Hyps d hlay
  have h524 := h.yamada_5_24 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101 hy.h5102
    hy.h59e hy.h520 hy.h5221
  have h5172 := h.yamada_5_17_2 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101
    hy.h5102
  refine le_antisymm ?_ (sup_le inf_le_left (h.S_map_le_yamadaR₄_R4 d hlay))
  rw [h524.2.1.1, h5172.2]
  exact sup_le le_sup_left (sup_le ((h.yamadaL₃_le_yamadaL₄ d hlay).trans le_sup_left)
    le_sup_right)

theorem yamadaR₆_le_normalizer_yamadaR₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaR₆ d t ≤ normalizer (yamadaR₄ d t : Set G) := by
  have hy := h.l6Hyps d hlay
  have h524 := h.yamada_5_24 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101 hy.h5102
    hy.h59e hy.h520 hy.h5221
  have hSR₄ : d.S.map L.subtype ≤ yamadaR₄ d t := h.S_map_le_yamadaR₄_R4 d hlay
  have hR₄S := h.yamadaR₄_eq_sup_yamadaL₄_L6T d hlay
  have hSL₄ : d.S.map L.subtype ≤ normalizer (yamadaL₄ d t : Set G) := fun s hs =>
    h524.2.1.2.2.1 (hSR₄ hs)
  have hset := coe_mul_of_right_le_normalizer_left (yamadaL₄ d t) (d.S.map L.subtype) hSL₄
  refine sup_le (fun y hyL => ?_) (fun s hs => le_normalizer (hSR₄ hs))
  refine mem_normalizer_fintype fun g hg => ?_
  rw [SetLike.mem_coe, hR₄S, ← SetLike.mem_coe, hset] at hg ⊢
  obtain ⟨x, hx, s, hs, rfl⟩ := Set.mem_mul.1 hg
  refine Set.mem_mul.2 ⟨y * x * y⁻¹ * (y * s * y⁻¹ * s⁻¹), mul_mem
    (h.conj_mem_yamadaL₄_of_mem_yamadaL₆_L6T d hlay hyL hx)
    (h.commutator_mem_yamadaL₄_of_mem_yamadaL₆_L6T d hlay hyL hs), s, hs, ?_⟩
  group

end Six

section Three

theorem mem_centralizer_inf_normalizer_S_of_mem_normalizer_L6T (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {X : Subgroup G}
    (hSX : d.S.map L.subtype ≤ X) (hXR₄ : X ≤ yamadaR₄ d t) {c : G}
    (hcX : c ∈ normalizer (X : Set G)) (hcC : c ∈ centralizer ({t} : Set G)) :
    c ∈ centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) := by
  have htS : t ∈ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) :=
    h.t_mem_normalizer_map d.S
  have hSC : d.S.map L.subtype ≤ centralizer ({t} : Set G) := h.S_le_centralizer d
  refine mem_inf.2 ⟨hcC, ?_⟩
  have hcL : c ∈ normalizer (L : Set G) := h.centralizer_le_normalizer hcC
  apply mem_normalizer_fintype
  intro x hx
  have hxL : x ∈ L := map_subtype_le _ hx
  have hcxX : c * x * c⁻¹ ∈ X := (mem_normalizer_iff.1 hcX x).1 (hSX hx)
  have hcxC : c * x * c⁻¹ ∈ centralizer ({t} : Set G) :=
    mul_mem (mul_mem hcC (hSC hx)) (inv_mem hcC)
  have hcxL : c * x * c⁻¹ ∈ L := (mem_normalizer_iff.1 hcL x).1 hxL
  have hmem := h.yamadaR₄_inf_centralizer_le d hlay (mem_inf.2 ⟨hXR₄ hcxX, hcxC⟩)
  rcases (h.mem_sup_zpowers_iff_of_normalizer htS).1 hmem with h1 | h1
  · exact h1
  · exfalso
    apply h.t_not_mem_L
    have h2 : t * (c * x * c⁻¹) * (c * x * c⁻¹)⁻¹ ∈ L :=
      mul_mem (map_subtype_le _ h1) (inv_mem hcxL)
    rwa [mul_inv_cancel_right] at h2

theorem yamada_5_27_3 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    normalizer (yamadaR₃ d t : Set G) = yamadaR₄ d t ⊔ (centralizer ({t} : Set G) ⊓
      normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) := by
  have hy := h.l6Hyps d hlay
  have h514 := h.yamada_5_14 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593
  have h5172 := h.yamada_5_17_2 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101
    hy.h5102
  have hR₃R₄ : yamadaR₃ d t ≤ yamadaR₄ d t := h514.2.2.2.2.1.1
  have hR₄R₃ : yamadaR₄ d t ≤ normalizer (yamadaR₃ d t : Set G) := h514.2.2.2.2.1.2
  have hSR₃ : d.S.map L.subtype ≤ yamadaR₃ d t := by
    rw [h5172.2]
    exact le_sup_right
  have hL₃R₃ : yamadaL₃ d t ≤ yamadaR₃ d t := h.yamadaL₃_le_yamadaR₃_D3 d hlay
  have hF₃R₃ : yamadaF₃ d t ≤ yamadaR₃ d t :=
    (inf_le_right : yamadaF₃ d t ≤ yamadaD₃ d t).trans
      ((inf_le_left : yamadaD₃ d t ≤ yamadaS₃ d t).trans
        (inf_le_left : yamadaS₃ d t ≤ yamadaR₃ d t))
  have htR₃ : t ∈ yamadaR₃ d t := h.t_mem_yamadaR₃ d hlay
  have htF₃ : t ∈ normalizer (yamadaF₃ d t : Set G) :=
    h.yamadaR₄_le_normalizer_yamadaF₃_R4 d hlay
      (h.t_mem_yamadaR₄ d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593)
  have htW₃ : t ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaL₃_le_normalizer_yamadaW₃ d hlay (h.t_mem_yamadaL₃_L6T d hlay)
  refine le_antisymm (fun g hg => ?_) (sup_le hR₄R₃
    (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₃ d hlay))
  have hgL₃ : g ∈ normalizer (yamadaL₃ d t : Set G) := by
    have hchar := hy.h5221.2.1
    have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      ((yamadaL₃ d t).subgroupOf (yamadaR₃ d t)) hg
    rwa [Subgroup.map_subgroupOf_eq_of_le hL₃R₃] at h1
  have hgF : g ∈ normalizer ((yamadaF₃ d t ⊔ zpowers t : Subgroup G) : Set G) := by
    have hchar := hy.h5221.1
    have h1 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      ((yamadaF₃ d t ⊔ zpowers t).subgroupOf (yamadaR₃ d t)) hg
    rwa [Subgroup.map_subgroupOf_eq_of_le (sup_le hF₃R₃ ((zpowers_le).2 htR₃))] at h1
  have hgY₂ : g ∈ normalizer (yamadaY₂ d t : Set G) := by
    have h1 := normalizer_le_normalizer_commutator_C8 (yamadaR₃ d t) hg
    rw [hy.h5221.2.2] at h1
    rw [← yamadaF₂_inf_centralizer d hy.h592]
    exact Common.mem_normalizer_inf h1 (mem_normalizer_centralizer_C8 h1)
  have hgM₃ : g ∈ normalizer (yamadaM₃ d t : Set G) :=
    Common.mem_normalizer_inf hgL₃ (mem_normalizer_centralizer_C8 hgY₂)
  have hgW₃ : g ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.normalizer_yamadaL₃_le_normalizer_yamadaW₃ d hlay hgL₃
  have hgt : g * t * g⁻¹ ∈ yamadaF₃ d t ⊔ zpowers t :=
    (mem_normalizer_iff.1 hgF t).1 (mem_sup_right (mem_zpowers t))
  obtain ⟨a, haF₃, hgta⟩ : ∃ a ∈ yamadaF₃ d t, g * t * g⁻¹ = t * a := by
    rcases (h.mem_sup_zpowers_iff_of_normalizer htF₃).1 hgt with h1 | h1
    · exfalso
      have h2 : g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ ∈ yamadaM₃ d t :=
        (mem_normalizer_iff.1 (inv_mem hgM₃) _).1 (mem_inf.1 h1).1
      rw [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at h2
      exact h.t_not_mem_yamadaM₃ d hlay h2
    · refine ⟨t * (g * t * g⁻¹), h1, ?_⟩
      calc g * t * g⁻¹ = (t * t) * (g * t * g⁻¹) := by rw [h.t_mul_t, one_mul]
        _ = t * (t * (g * t * g⁻¹)) := mul_assoc _ _ _
  obtain ⟨r, hrL₄, w, hwW₃, hrw⟩ := h.exists_mem_yamadaL₄_conj_eq d hlay haF₃
  have hrR₄ : r ∈ yamadaR₄ d t := (mem_inf.1 hrL₄).1
  have hrN : r ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaR₄_le_normalizer_yamadaW₃_R4 d hlay hrR₄
  have hta' : t * a = r * t * r⁻¹ * w⁻¹ := by
    rw [hrw]
    group
  have hkey : r⁻¹ * g * t * (r⁻¹ * g)⁻¹ = t * (r⁻¹ * w⁻¹ * r) := by
    calc r⁻¹ * g * t * (r⁻¹ * g)⁻¹ = r⁻¹ * (g * t * g⁻¹) * r := by group
      _ = r⁻¹ * (t * a) * r := by rw [hgta]
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
  have hlR₃ : l ∈ yamadaR₃ d t := hL₃R₃ hl
  have hcC : c ∈ centralizer ({t} : Set G) := (mem_inf.1 hc).1
  have hcN : c ∈ normalizer (yamadaR₃ d t : Set G) := by
    have hc' : c = l⁻¹ * (r⁻¹ * g) := by rw [← hlc]; group
    rw [hc']
    exact mul_mem (inv_mem (le_normalizer hlR₃)) (mul_mem (inv_mem (hR₄R₃ hrR₄)) hg)
  have hcNCS := h.mem_centralizer_inf_normalizer_S_of_mem_normalizer_L6T d hlay hSR₃ hR₃R₄ hcN hcC
  have hg_eq : g = r * l * c := by
    rw [mul_assoc, hlc]
    group
  rw [hg_eq]
  exact mul_mem (mem_sup_left (mul_mem hrR₄ (hR₃R₄ hlR₃))) (mem_sup_right hcNCS)

end Three

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
