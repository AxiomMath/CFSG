module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Two

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open scoped commutatorElement Pointwise

section Defs

variable {G : Type} [Group G] {L : Subgroup G} {q : ℕ}

@[expose] noncomputable def yamadaR₃ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaR₅ d t ⊓ normalizer ((yamadaW₁ d t ⊔ zpowers t : Subgroup G) : Set G)

@[expose] noncomputable def yamadaR₄ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  yamadaR₅ d t ⊓ normalizer ((yamadaF₁ d t ⊔ zpowers t : Subgroup G) : Set G)

theorem yamadaC₁_le_yamadaC₅ [Finite G] (d : TrialityD4Data L q) (t : G) :
    yamadaC₁ d t ≤ yamadaC₅ d t :=
  LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_normalizer (fun _ hg => hg)
    (LieType.BorelTits.pCoreOf_isPGroup 2 _)

end Defs

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem M_inf_D_le_F : d.M ⊓ d.D ≤ d.F := by
  intro x hx
  obtain ⟨hxM, hxD⟩ := mem_inf.1 hx
  have hU₁F : d.U₁ ≤ normalizer (d.F : Set X) := d.U₁_le_S.trans d.S_le_normalizer_F
  rw [show d.M = d.U₁ ⊔ d.F from rfl, ← SetLike.mem_coe,
    coe_mul_of_left_le_normalizer_right _ _ hU₁F, Set.mem_mul] at hxM
  obtain ⟨u, hu, n, hn, rfl⟩ := hxM
  obtain ⟨a, rfl⟩ := hu
  have ha : d.x₁ a ∈ d.D := by
    have := mul_mem hxD (inv_mem (d.F_le_D hn))
    rwa [mul_inv_cancel_right] at this
  rw [d.x₁_mem_D_iff.1 ha, d.x₁_zero, one_mul]
  exact hn

end TrialityD4Data

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Basic

theorem S_le_normalizer_yamadaC₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    d.S.map L.subtype ≤ normalizer (yamadaC₁ d t : Set G) := fun _ hs =>
  le_normalizer_yamadaC₁ d t (h.centralizer_inf_normalizer_V_le d
    ⟨h.S_le_centralizer d hs, map_le_normalizer_map d.S_le_normalizer_V hs⟩)

theorem yamadaR₅_le_normalizer_yamadaC₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaR₅ d t ≤ normalizer (yamadaC₁ d t : Set G) :=
  sup_le (yamadaC₅_le d t) (h.S_le_normalizer_yamadaC₁ d)

theorem coe_yamadaR₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    ((yamadaR₅ d t : Subgroup G) : Set G) =
      (yamadaC₅ d t : Set G) * ((d.S.map L.subtype : Subgroup G) : Set G) :=
  coe_mul_of_right_le_normalizer_left _ _
    ((h.S_le_normalizer_yamadaC₁ d).trans (le_normalizer_yamadaC₅ d t))

theorem t_mem_yamadaR₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) : t ∈ yamadaR₅ d t :=
  mem_sup_left (yamadaC₁_le_yamadaC₅ d t (h.t_mem_yamadaC₁ d))

end Basic

section Main

variable (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hNH : NormalizerHyp d t)
  (h561 : yamadaC₁ d t = yamadaD₁ d t ⊔ zpowers t ∧ t ∉ yamadaD₁ d t ∧
    (normalizer (d.V : Set L)).map L.subtype ≤ normalizer (yamadaD₁ d t : Set G))
  (h562 : IsElemAbelian 2 (yamadaV₁ d t) ∧ Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2 ∧
    yamadaV₁ d t ⊓ centralizer ({t} : Set G) = d.V.map L.subtype ∧ yamadaV₁ d t ≤ yamadaF₁ d t)
  (h591 : yamadaL₂ d t = yamadaM₂ d t ⊔ zpowers t ∧ t ∉ yamadaM₂ d t ∧
    yamadaR₂ d t = yamadaS₂ d t ⊔ zpowers t ∧ t ∉ yamadaS₂ d t)
  (h592 : yamadaV₁ d t ⊓ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom = ⊥ ∧
    Nat.card (yamadaY₂ d t) = (2 ^ f) ^ 4 ∧ IsMulCommutative (yamadaY₂ d t) ∧
    yamadaM₂ d t ⊓ centralizer (yamadaM₂ d t : Set G) = yamadaY₂ d t ∧
    yamadaY₂ d t ⊓ centralizer ({t} : Set G) = d.Y.map L.subtype)
  (h593 : (Subgroup.upperCentralSeries (yamadaS₂ d t) 1).map (yamadaS₂ d t).subtype =
      yamadaV₁ d t ∧
    (Subgroup.upperCentralSeries (yamadaS₂ d t) 2).map (yamadaS₂ d t).subtype = yamadaY₂ d t)

omit [Finite G] in
include h593 in
theorem mul_comm_of_mem_S_of_mem_yamadaV₁ {s v : G} (hs : s ∈ d.S.map L.subtype)
    (hv : v ∈ yamadaV₁ d t) : s * v = v * s := by
  rw [← h593.1, Subgroup.upperCentralSeries_one] at hv
  obtain ⟨v', hv', rfl⟩ := hv
  exact congrArg Subtype.val ((mem_center_iff.1 hv') ⟨s, mem_sup_left hs⟩)

include h593 in
theorem S_le_normalizer_yamadaV₁ : d.S.map L.subtype ≤ normalizer (yamadaV₁ d t : Set G) :=
  fun s hs => mem_normalizer_fintype fun v hv => by
    rw [mul_comm_of_mem_S_of_mem_yamadaV₁ d h593 hs hv, mul_inv_cancel_right]
    exact hv

include h h561 h562 in
theorem yamadaF₁_eq_sup : yamadaF₁ d t = d.F.map L.subtype ⊔ yamadaV₁ d t := by
  refine le_antisymm (fun x hx => ?_) (sup_le (fun x hx => ?_) h562.2.2.2)
  · obtain ⟨hxM₁, hxD₁⟩ := mem_inf.1 hx
    obtain ⟨hxL₂, -⟩ := mem_inf.1 hxM₁
    obtain ⟨n, hn, v, hv, rfl⟩ := h.exists_mul_of_mem_yamadaD₁ d h561 h562 hxD₁
    have hvL₂ : v ∈ yamadaL₂ d t := (h562.2.2.2 hv).1.1
    have hnL₂ : n ∈ yamadaL₂ d t := by
      have := mul_mem hxL₂ (inv_mem hvL₂)
      rwa [mul_inv_cancel_right] at this
    have hnL : n ∈ L := map_subtype_le _ hn
    have hnM : n ∈ d.M.map L.subtype := by
      have h1 : n ∈ yamadaL₂ d t ⊓ centralizer ({t} : Set G) := ⟨hnL₂, h.L_le_centralizer hnL⟩
      rw [(h.yamada_5_3_2 d).2.2.2.2.1] at h1
      rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 h1 with h2 | h2
      · exact h2
      · exfalso
        refine h.t_not_mem_L ?_
        have := mul_mem (map_subtype_le _ h2) (inv_mem hnL)
        rwa [mul_inv_cancel_right] at this
    obtain ⟨n', hn', rfl⟩ := hn
    have hn'M : n' ∈ d.M := coe_mem_map_subtype_iff_D4.1 hnM
    exact mul_mem (mem_sup_left ⟨n', d.M_inf_D_le_F ⟨hn'M, hn'⟩, rfl⟩) (mem_sup_right hv)
  · have hxF : x ∈ d.F.map L.subtype := hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact h.tM_le_yamadaL₂ d (mem_sup_left ⟨y, d.F_le_M hy, rfl⟩)
    · exact mem_sup_left ⟨y, d.F_le_S hy, rfl⟩
    · exact D_le_yamadaD₁ d t (map_mono d.F_le_D hxF)

include h hNH h561 h562 h591 h592 h593 in
theorem yamadaR₅_le_normalizer_of_le {H : Subgroup G} (hVH : yamadaV₁ d t ≤ H)
    (hHD : H ≤ yamadaD₁ d t) (hS : d.S.map L.subtype ≤ normalizer (H : Set G)) :
    yamadaR₅ d t ≤ normalizer (H : Set G) := by
  have hCQ := h.yamadaC₅_eq_yamadaQ₅ d hNH h561 h562 h591 h592 h593
  refine sup_le (fun c hc => mem_normalizer_fintype fun x hx => ?_) hS
  have h1 := (mem_yamadaQ₅.1 (hCQ ▸ hc)).2 x (hHD hx)
  rw [show c * x * c⁻¹ = c * x * c⁻¹ * x⁻¹ * x by group]
  exact mul_mem (hVH h1) hx

include h h561 h562 in
theorem yamadaD₁_le_normalizer_of_le {H : Subgroup G} (hVH : yamadaV₁ d t ≤ H)
    (hHD : H ≤ yamadaD₁ d t) : yamadaD₁ d t ≤ normalizer (H : Set G) := fun δ hδ =>
  mem_normalizer_fintype fun x hx => by
    have h1 := h.commutatorElement_mem_yamadaV₁_of_mem_yamadaD₁ d h561 h562 hδ (hHD hx)
    rw [show δ * x * δ⁻¹ = δ * x * δ⁻¹ * x⁻¹ * x by group]
    exact mul_mem (hVH h1) hx

include h hNH h561 h562 in
theorem mem_inf_normalizer_iff {H : Subgroup G} (hHD : H ≤ yamadaD₁ d t)
    (hH5 : yamadaR₅ d t ≤ normalizer (H : Set G)) {x : G} :
    x ∈ yamadaR₅ d t ⊓ normalizer ((H ⊔ zpowers t : Subgroup G) : Set G) ↔
      x ∈ yamadaR₅ d t ∧ t * x * t * x⁻¹ ∈ H := by
  have htH : t ∈ normalizer (H : Set G) := hH5 (h.t_mem_yamadaR₅ d)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  constructor
  · rintro ⟨hx5, hxN⟩
    refine ⟨hx5, ?_⟩
    have h1 : x * t * x⁻¹ ∈ H ⊔ zpowers t :=
      (mem_normalizer_iff.1 hxN t).1 (mem_sup_right (mem_zpowers t))
    rcases (mem_sup_zpowers_iff_of_D4 h.t_mul_t htH).1 h1 with h2 | ⟨a, ha, h2⟩
    · exfalso
      apply h561.2.1
      have hxD := hNH.1
        (h.yamadaR₅_le_normalizer_yamadaC₁ d hx5)
      have := (mem_normalizer_iff.1 (inv_mem hxD) _).1 (hHD h2)
      rwa [show x⁻¹ * (x * t * x⁻¹) * x⁻¹⁻¹ = t by group] at this
    · rw [show t * x * t * x⁻¹ = t * (x * t * x⁻¹) by group, h2]
      have := (mem_normalizer_iff.1 htH a).1 ha
      rw [htinv] at this
      rw [← mul_assoc]
      exact this
  · rintro ⟨hx5, hκ⟩
    refine ⟨hx5, mem_normalizer_fintype fun z hz => ?_⟩
    have hxH := hH5 hx5
    have hxt : x * t * x⁻¹ = t * (t * x * t * x⁻¹) := by
      rw [show t * (t * x * t * x⁻¹) = (t * t) * x * t * x⁻¹ by group, h.t_mul_t, one_mul]
    rcases (mem_sup_zpowers_iff_of_D4 h.t_mul_t htH).1 hz with hz | ⟨w, hw, rfl⟩
    · exact mem_sup_left ((mem_normalizer_iff.1 hxH z).1 hz)
    · rw [show x * (w * t) * x⁻¹ = x * w * x⁻¹ * (x * t * x⁻¹) by group, hxt]
      exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 hxH w).1 hw))
        (mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hκ))

include h hNH h561 h562 h591 h592 h593 in
theorem exists_mem_inf_normalizer_conj_eq {H : Subgroup G} (hVH : yamadaV₁ d t ≤ H)
    (hHD : H ≤ yamadaD₁ d t) (hH5 : yamadaR₅ d t ≤ normalizer (H : Set G)) {w : G}
    (hw : w ∈ H) : ∃ x ∈ yamadaR₅ d t ⊓ normalizer ((H ⊔ zpowers t : Subgroup G) : Set G),
      ∃ v ∈ yamadaV₁ d t, x * t * x⁻¹ = t * w * v := by
  have hCQ := h.yamadaC₅_eq_yamadaQ₅ d hNH h561 h562 h591 h592 h593
  obtain ⟨x, hx, v, hv, e⟩ :=
    h.exists_mem_yamadaQ₅_conj_eq d hNH h561 h562 h591 h592 h593 (hHD hw)
  refine ⟨x, (h.mem_inf_normalizer_iff d hNH h561 h562 hHD hH5).2
    ⟨mem_sup_left (hCQ ▸ hx), ?_⟩, v, hv, e⟩
  rw [show t * x * t * x⁻¹ = t * (x * t * x⁻¹) by group, e, ← mul_assoc, ← mul_assoc,
    h.t_mul_t, one_mul]
  exact mul_mem hw (hVH hv)

include h hNH h561 h562 h591 h592 h593 in
theorem commutatorElement_mem_of_mem_yamadaR₅ {A B : Subgroup L} (hAD : A ≤ d.D) (hBA : B ≤ A)
    (hSB : d.S ≤ normalizer (B : Set L)) (hAB : ⁅d.S, A⁆ ≤ B) {x y : G}
    (hx : x ∈ A.map L.subtype ⊔ yamadaV₁ d t) (hy : y ∈ yamadaR₅ d t) :
    x * y * x⁻¹ * y⁻¹ ∈ B.map L.subtype ⊔ yamadaV₁ d t := by
  have hCQ := h.yamadaC₅_eq_yamadaQ₅ d hNH h561 h562 h591 h592 h593
  have hADG : A.map L.subtype ≤ yamadaD₁ d t := (map_mono hAD).trans (D_le_yamadaD₁ d t)
  have hSA : d.S ≤ normalizer (A : Set L) := le_normalizer_of_commutator_le hBA hAB
  have hAN : A.map L.subtype ≤ normalizer (yamadaV₁ d t : Set G) := hADG.trans
    (le_normalizer.trans (normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t))
  have hNA : ∀ s ∈ d.S.map L.subtype, s ∈ normalizer ((A.map L.subtype ⊔ yamadaV₁ d t :
      Subgroup G) : Set G) := fun s hs => Common.mem_normalizer_sup
    (map_le_normalizer_map hSA hs) (S_le_normalizer_yamadaV₁ d h593 hs)
  have hNB : ∀ s ∈ d.S.map L.subtype, s ∈ normalizer ((B.map L.subtype ⊔ yamadaV₁ d t :
      Subgroup G) : Set G) := fun s hs => Common.mem_normalizer_sup
    (map_le_normalizer_map hSB hs) (S_le_normalizer_yamadaV₁ d h593 hs)
  have hK : ∀ g ∈ yamadaR₅ d t, ∀ z ∈ A.map L.subtype ⊔ yamadaV₁ d t,
      g * z * g⁻¹ * z⁻¹ ∈ B.map L.subtype ⊔ yamadaV₁ d t := by
    have hR₅ : yamadaR₅ d t ≤ Common.centralizerMod
        (normalizer ((A.map L.subtype ⊔ yamadaV₁ d t : Subgroup G) : Set G) ⊓
          normalizer ((B.map L.subtype ⊔ yamadaV₁ d t : Subgroup G) : Set G))
        (A.map L.subtype ⊔ yamadaV₁ d t) (B.map L.subtype ⊔ yamadaV₁ d t)
        (fun _ hg y hy => (mem_normalizer_iff.1 (mem_inf.1 hg).1 y).1 hy)
        (fun _ hg b hb => (mem_normalizer_iff.1 (mem_inf.1 hg).2 b).1 hb) := by
      refine sup_le (fun c hc => ?_) (fun s hs => ?_)
      · have hc' := (mem_yamadaQ₅.1 (hCQ ▸ hc)).2
        have hcN : ∀ {H : Subgroup G}, yamadaV₁ d t ≤ H → H ≤ yamadaD₁ d t →
            c ∈ normalizer (H : Set G) := fun hVH hHD => mem_normalizer_fintype fun z hz => by
          rw [show c * z * c⁻¹ = c * z * c⁻¹ * z⁻¹ * z by group]
          exact mul_mem (hVH (hc' z (hHD hz))) hz
        refine ⟨mem_inf.2 ⟨hcN le_sup_right (sup_le hADG (yamadaV₁_le_yamadaD₁ d t)),
          hcN le_sup_right (sup_le ((map_mono hBA).trans hADG) (yamadaV₁_le_yamadaD₁ d t))⟩,
          fun z hz => mem_sup_right (hc' z (sup_le hADG (yamadaV₁_le_yamadaD₁ d t) hz))⟩
      · refine ⟨mem_inf.2 ⟨hNA s hs, hNB s hs⟩, fun z hz => ?_⟩
        rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hAN, Set.mem_mul] at hz
        obtain ⟨a, ha, v, hv, rfl⟩ := hz
        have hsv : s * v = v * s := mul_comm_of_mem_S_of_mem_yamadaV₁ d h593 hs hv
        have hvs : v * s⁻¹ * v⁻¹ = s⁻¹ := by
          calc v * s⁻¹ * v⁻¹ = s⁻¹ * (s * v) * s⁻¹ * v⁻¹ := by group
            _ = s⁻¹ * (v * s) * s⁻¹ * v⁻¹ := by rw [hsv]
            _ = s⁻¹ := by group
        have e : s * (a * v) * s⁻¹ * (a * v)⁻¹ = s * a * s⁻¹ * a⁻¹ := by
          calc s * (a * v) * s⁻¹ * (a * v)⁻¹ = s * a * (v * s⁻¹ * v⁻¹) * a⁻¹ := by group
            _ = s * a * s⁻¹ * a⁻¹ := by rw [hvs]
        rw [e]
        obtain ⟨s', hs', rfl⟩ := hs
        obtain ⟨a', ha', rfl⟩ := ha
        have h1 := hAB (commutator_mem_commutator hs' ha')
        exact mem_sup_left (mem_map_of_mem L.subtype h1)
    exact fun g hg z hz => (Common.mem_centralizerMod.1 (hR₅ hg)).2 z hz
  have h1 := hK y hy x hx
  have e : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem h1

include h hNH h561 h562 in
theorem crossed_conj_mem {H H' : Subgroup G} (hVH : yamadaV₁ d t ≤ H) (hHD : H ≤ yamadaD₁ d t)
    (hH5 : yamadaR₅ d t ≤ normalizer (H : Set G))
    (hcomm : ∀ x ∈ H', ∀ y ∈ yamadaR₅ d t, x * y * x⁻¹ * y⁻¹ ∈ H) {g x : G}
    (hg : g ∈ yamadaR₅ d t) (hκg : t * g * t * g⁻¹ ∈ H') (hx : x ∈ yamadaR₅ d t)
    (hκx : t * x * t * x⁻¹ ∈ H) : t * (g * x * g⁻¹) * t * (g * x * g⁻¹)⁻¹ ∈ H := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have hκgD := h.crossed_mem_yamadaD₁ d hNH h561 h562 (h.yamadaR₅_le_normalizer_yamadaC₁ d hg)
  have e : t * (g * x * g⁻¹) * t⁻¹ * (g * x * g⁻¹)⁻¹ =
      ((t * g * t⁻¹ * g⁻¹) * (g * (t * x * t⁻¹ * x⁻¹) * g⁻¹) * (t * g * t⁻¹ * g⁻¹)⁻¹) *
        ((t * g * t⁻¹ * g⁻¹) * (g * x * g⁻¹) * (t * g * t⁻¹ * g⁻¹)⁻¹ * (g * x * g⁻¹)⁻¹) := by
    group
  rw [htinv] at e
  rw [e]
  refine mul_mem ?_ (hcomm _ hκg _ (mul_mem (mul_mem hg hx) (inv_mem hg)))
  exact (mem_normalizer_iff.1 (h.yamadaD₁_le_normalizer_of_le d h561 h562 hVH hHD hκgD) _).1
    ((mem_normalizer_iff.1 (hH5 hg) _).1 hκx)

omit [Finite G] in
theorem yamadaY₁_le_yamadaW₁ : yamadaY₁ d t ≤ yamadaW₁ d t :=
  sup_le_sup_right (map_mono d.Y_le_W) _

include h h561 h562 in
theorem yamadaW₁_le_yamadaF₁ : yamadaW₁ d t ≤ yamadaF₁ d t := by
  rw [h.yamadaF₁_eq_sup d h561 h562]
  exact sup_le_sup_right (map_mono d.W_le_F) _

omit [Finite G] in
theorem yamadaF₁_le_yamadaD₁ : yamadaF₁ d t ≤ yamadaD₁ d t := inf_le_right

omit [Finite G] in
theorem yamadaW₁_le_yamadaD₁ : yamadaW₁ d t ≤ yamadaD₁ d t :=
  sup_le ((map_mono (d.W_le_F.trans d.F_le_D)).trans (D_le_yamadaD₁ d t))
    (yamadaV₁_le_yamadaD₁ d t)

omit [Finite G] in
theorem yamadaY₁_le_yamadaD₁ : yamadaY₁ d t ≤ yamadaD₁ d t :=
  (yamadaY₁_le_yamadaW₁ d).trans (yamadaW₁_le_yamadaD₁ d)

include h hNH h561 h562 h591 h592 h593 in
theorem yamadaR₅_le_normalizer_yamadaY₁ : yamadaR₅ d t ≤ normalizer (yamadaY₁ d t : Set G) :=
  h.yamadaR₅_le_normalizer_of_le d hNH h561 h562 h591 h592 h593 le_sup_right
    (yamadaY₁_le_yamadaD₁ d) fun _ hs => Common.mem_normalizer_sup
      (map_le_normalizer_map d.S_le_normalizer_Y hs) (S_le_normalizer_yamadaV₁ d h593 hs)

include h hNH h561 h562 h591 h592 h593 in
theorem yamadaR₅_le_normalizer_yamadaW₁ : yamadaR₅ d t ≤ normalizer (yamadaW₁ d t : Set G) :=
  h.yamadaR₅_le_normalizer_of_le d hNH h561 h562 h591 h592 h593 le_sup_right
    (yamadaW₁_le_yamadaD₁ d) fun _ hs => Common.mem_normalizer_sup
      (map_le_normalizer_map d.S_le_normalizer_W hs) (S_le_normalizer_yamadaV₁ d h593 hs)

include h hNH h561 h562 h591 h592 h593 in
theorem yamadaR₅_le_normalizer_yamadaF₁ : yamadaR₅ d t ≤ normalizer (yamadaF₁ d t : Set G) := by
  have hF := h.yamadaF₁_eq_sup d h561 h562
  refine h.yamadaR₅_le_normalizer_of_le d hNH h561 h562 h591 h592 h593 h562.2.2.2
    (yamadaF₁_le_yamadaD₁ d) fun _ hs => ?_
  rw [hF]
  exact Common.mem_normalizer_sup (map_le_normalizer_map d.S_le_normalizer_F hs)
    (S_le_normalizer_yamadaV₁ d h593 hs)

include h hNH h561 h562 h591 h592 h593 in
theorem commutatorElement_mem_yamadaY₁ {x y : G} (hx : x ∈ yamadaW₁ d t)
    (hy : y ∈ yamadaR₅ d t) : x * y * x⁻¹ * y⁻¹ ∈ yamadaY₁ d t :=
  h.commutatorElement_mem_of_mem_yamadaR₅ d hNH h561 h562 h591 h592 h593
    (d.W_le_F.trans d.F_le_D) d.Y_le_W d.S_le_normalizer_Y d.commutator_S_W hx hy

include h hNH h561 h562 h591 h592 h593 in
theorem commutatorElement_mem_yamadaW₁ {x y : G} (hx : x ∈ yamadaF₁ d t)
    (hy : y ∈ yamadaR₅ d t) : x * y * x⁻¹ * y⁻¹ ∈ yamadaW₁ d t := by
  rw [h.yamadaF₁_eq_sup d h561 h562] at hx
  exact h.commutatorElement_mem_of_mem_yamadaR₅ d hNH h561 h562 h591 h592 h593 d.F_le_D
    d.W_le_F d.S_le_normalizer_W d.commutator_S_F hx hy

include h hNH h561 h562 h591 h592 h593 in
theorem commutatorElement_mem_yamadaF₁ {x y : G} (hx : x ∈ yamadaD₁ d t)
    (hy : y ∈ yamadaR₅ d t) : x * y * x⁻¹ * y⁻¹ ∈ yamadaF₁ d t := by
  rw [h.yamadaD₁_eq_sup d h561 h562] at hx
  rw [h.yamadaF₁_eq_sup d h561 h562]
  exact h.commutatorElement_mem_of_mem_yamadaR₅ d hNH h561 h562 h591 h592 h593 le_rfl
    d.F_le_D d.S_le_normalizer_F d.commutator_S_D hx hy

include h hNH h561 h562 h591 h592 h593 in
theorem yamadaR₂_le_yamadaR₅ : yamadaR₂ d t ≤ yamadaR₅ d t := by
  have hCQ := h.yamadaC₅_eq_yamadaQ₅ d hNH h561 h562 h591 h592 h593
  rw [h591.2.2.1]
  refine sup_le (sup_le le_sup_right ?_) ((zpowers_le).2 (h.t_mem_yamadaR₅ d))
  exact (hCQ ▸ h.yamadaY₂_le_yamadaQ₅ d h561 h562 h591 h593).trans le_sup_left

include h hNH h561 h562 h591 h592 h593 in
theorem yamadaR₂_eq_inf_normalizer : yamadaR₂ d t =
    yamadaR₅ d t ⊓ normalizer ((yamadaY₁ d t ⊔ zpowers t : Subgroup G) : Set G) := by
  have hCQ := h.yamadaC₅_eq_yamadaQ₅ d hNH h561 h562 h591 h592 h593
  have hY₁5 := h.yamadaR₅_le_normalizer_yamadaY₁ d hNH h561 h562 h591 h592 h593
  have hiff := fun {x : G} =>
    h.mem_inf_normalizer_iff d hNH h561 h562 (yamadaY₁_le_yamadaD₁ d) hY₁5 (x := x)
  apply le_antisymm
  · intro x hx
    refine hiff.2 ⟨h.yamadaR₂_le_yamadaR₅ d hNH h561 h562 h591 h592 h593 hx, ?_⟩
    have h1 := h.crossed_mem_Y_of_mem_yamadaR₂ d (inv_mem hx)
    rw [inv_inv] at h1
    have h2 := (mem_normalizer_iff.1 (h.t_mem_normalizer_map d.Y) _).1 h1
    rw [show t * (x * t * x⁻¹ * t) * t⁻¹ = t * x * t * x⁻¹ by group] at h2
    exact mem_sup_left h2
  · intro x hx
    obtain ⟨hx5, hκ⟩ := hiff.1 hx
    rw [← SetLike.mem_coe, h.coe_yamadaR₅ d, Set.mem_mul] at hx5
    obtain ⟨c, hc, s, hs, rfl⟩ := hx5
    have hst : s * t = t * s := mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)
    have hκc : t * c * t * c⁻¹ ∈ yamadaY₁ d t := by
      have e : t * (c * s) * t * (c * s)⁻¹ = t * c * t * c⁻¹ := by
        calc t * (c * s) * t * (c * s)⁻¹ = t * c * (s * t) * s⁻¹ * c⁻¹ := by group
          _ = t * c * (t * s) * s⁻¹ * c⁻¹ := by rw [hst]
          _ = t * c * t * c⁻¹ := by group
      rwa [e] at hκ
    have hYD : d.Y.map L.subtype ≤ yamadaD₁ d t :=
      (map_mono (d.Y_le_W.trans (d.W_le_F.trans d.F_le_D))).trans (D_le_yamadaD₁ d t)
    have hYV : d.Y.map L.subtype ≤ normalizer (yamadaV₁ d t : Set G) :=
      hYD.trans (le_normalizer.trans (normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t))
    rw [show yamadaY₁ d t = d.Y.map L.subtype ⊔ yamadaV₁ d t from rfl, ← SetLike.mem_coe,
      coe_mul_of_left_le_normalizer_right _ _ hYV, Set.mem_mul] at hκc
    obtain ⟨y, hy, v₁, hv₁, hyv⟩ := hκc
    obtain ⟨a, ha, hat⟩ := h.exists_mem_yamadaY₂_conj_eq d h591 h592 hy
    have haQ := h.yamadaY₂_le_yamadaQ₅ d h561 h562 h591 h593 ha
    have hcQ : c ∈ yamadaQ₅ d t := hCQ ▸ hc
    have hcN := (mem_yamadaQ₅.1 hcQ).1.1
    have haN := (mem_yamadaQ₅.1 haQ).1.1
    have hκa : t * a * t * a⁻¹ = y := by
      rw [show t * a * t * a⁻¹ = t * (a * t * a⁻¹) by group, hat, ← mul_assoc, h.t_mul_t,
        one_mul]
    have hκ1 : t * (a * a⁻¹) * t * (a * a⁻¹)⁻¹ = 1 := by
      rw [mul_inv_cancel, mul_one, inv_one, mul_one, h.t_mul_t]
    have h1 := h.crossed_mul_mem d hNH h561 h562 haQ (inv_mem haN)
    rw [hκ1, mul_one, hκa] at h1
    have h1' := (inv_mem_iff).1 h1
    have hyN : y ∈ normalizer (yamadaV₁ d t : Set G) := hYV hy
    have h2 : (t * a⁻¹ * t * a⁻¹⁻¹) * (t * c * t * c⁻¹) ∈ yamadaV₁ d t := by
      rw [← hyv]
      have e : (t * a⁻¹ * t * a⁻¹⁻¹) * (y * v₁) =
          y⁻¹ * (y * (t * a⁻¹ * t * a⁻¹⁻¹)) * y⁻¹⁻¹ * v₁ := by group
      rw [e]
      exact mul_mem ((mem_normalizer_iff.1 (inv_mem hyN) _).1 h1') hv₁
    have h3 := h.crossed_mul_mem d hNH h561 h562 (inv_mem haQ) hcN
    have h4 : t * (a⁻¹ * c) * t * (a⁻¹ * c)⁻¹ ∈ yamadaV₁ d t := by
      have := mul_mem h2 h3
      rwa [mul_inv_cancel_left] at this
    have h5 := h.mem_yamadaC₁_of_crossed_mem d hNH h561 h562 (mul_mem (inv_mem haQ) hcQ) h4
    have haR₂ : a ∈ yamadaR₂ d t := by
      rw [h591.2.2.1]
      exact mem_sup_left (mem_sup_right ha)
    have hcR₂ : c ∈ yamadaR₂ d t := by
      have := mul_mem haR₂ (h.yamadaC₁_le_yamadaR₂ d h5)
      rwa [mul_inv_cancel_left] at this
    exact mul_mem hcR₂ (mem_sup_right hs)

include h hNH h561 h562 in
theorem inf_normalizer_le_and_le_normalizer {H H' : Subgroup G} (hVH : yamadaV₁ d t ≤ H)
    (hHH' : H ≤ H') (hH'D : H' ≤ yamadaD₁ d t) (hH5 : yamadaR₅ d t ≤ normalizer (H : Set G))
    (hH'5 : yamadaR₅ d t ≤ normalizer (H' : Set G))
    (hcomm : ∀ x ∈ H', ∀ y ∈ yamadaR₅ d t, x * y * x⁻¹ * y⁻¹ ∈ H) :
    yamadaR₅ d t ⊓ normalizer ((H ⊔ zpowers t : Subgroup G) : Set G) ≤
        yamadaR₅ d t ⊓ normalizer ((H' ⊔ zpowers t : Subgroup G) : Set G) ∧
      yamadaR₅ d t ⊓ normalizer ((H' ⊔ zpowers t : Subgroup G) : Set G) ≤
        normalizer ((yamadaR₅ d t ⊓ normalizer ((H ⊔ zpowers t : Subgroup G) : Set G) :
          Subgroup G) : Set G) := by
  have hiff := fun {x : G} =>
    h.mem_inf_normalizer_iff d hNH h561 h562 (hHH'.trans hH'D) hH5 (x := x)
  have hiff' := fun {x : G} => h.mem_inf_normalizer_iff d hNH h561 h562 hH'D hH'5 (x := x)
  refine ⟨fun x hx => ?_, fun g hg => mem_normalizer_fintype fun x hx => ?_⟩
  · obtain ⟨hx5, hκ⟩ := hiff.1 hx
    exact hiff'.2 ⟨hx5, hHH' hκ⟩
  · obtain ⟨hg5, hκg⟩ := hiff'.1 hg
    obtain ⟨hx5, hκx⟩ := hiff.1 hx
    exact hiff.2 ⟨mul_mem (mul_mem hg5 hx5) (inv_mem hg5), h.crossed_conj_mem d hNH h561 h562
      hVH (hHH'.trans hH'D) hH5 hcomm hg5 hκg hx5 hκx⟩

include h hNH h561 h562 h591 h592 h593 in
theorem yamada_5_14 :
    ((∀ x ∈ yamadaR₃ d t, ∃ w ∈ yamadaW₁ d t, x * t * x⁻¹ = t * w) ∧
      ∀ w ∈ yamadaW₁ d t, ∃ x ∈ yamadaR₃ d t, ∃ v ∈ yamadaV₁ d t, x * t * x⁻¹ = t * w * v) ∧
    ((∀ x ∈ yamadaR₄ d t, ∃ w ∈ yamadaF₁ d t, x * t * x⁻¹ = t * w) ∧
      ∀ w ∈ yamadaF₁ d t, ∃ x ∈ yamadaR₄ d t, ∃ v ∈ yamadaV₁ d t, x * t * x⁻¹ = t * w * v) ∧
    yamadaR₂ d t =
      yamadaR₅ d t ⊓ normalizer ((yamadaY₁ d t ⊔ zpowers t : Subgroup G) : Set G) ∧
    (yamadaR₂ d t ≤ yamadaR₃ d t ∧ yamadaR₃ d t ≤ normalizer (yamadaR₂ d t : Set G)) ∧
    (yamadaR₃ d t ≤ yamadaR₄ d t ∧ yamadaR₄ d t ≤ normalizer (yamadaR₃ d t : Set G)) ∧
    (yamadaR₄ d t ≤ yamadaR₅ d t ∧ yamadaR₅ d t ≤ normalizer (yamadaR₄ d t : Set G)) := by
  have hY₁5 := h.yamadaR₅_le_normalizer_yamadaY₁ d hNH h561 h562 h591 h592 h593
  have hW₁5 := h.yamadaR₅_le_normalizer_yamadaW₁ d hNH h561 h562 h591 h592 h593
  have hF₁5 := h.yamadaR₅_le_normalizer_yamadaF₁ d hNH h561 h562 h591 h592 h593
  have hR₂ := h.yamadaR₂_eq_inf_normalizer d hNH h561 h562 h591 h592 h593
  have hcrossed : ∀ {H : Subgroup G}, H ≤ yamadaD₁ d t → yamadaR₅ d t ≤ normalizer (H : Set G) →
      ∀ x ∈ yamadaR₅ d t ⊓ normalizer ((H ⊔ zpowers t : Subgroup G) : Set G),
        ∃ w ∈ H, x * t * x⁻¹ = t * w := fun hHD hH5 x hx => by
    obtain ⟨-, hκ⟩ := (h.mem_inf_normalizer_iff d hNH h561 h562 hHD hH5).1 hx
    refine ⟨_, hκ, ?_⟩
    rw [show t * (t * x * t * x⁻¹) = (t * t) * x * t * x⁻¹ by group, h.t_mul_t, one_mul]
  have h23 := h.inf_normalizer_le_and_le_normalizer d hNH h561 h562 le_sup_right
    (yamadaY₁_le_yamadaW₁ d) (yamadaW₁_le_yamadaD₁ d) hY₁5 hW₁5
    fun x hx y hy => h.commutatorElement_mem_yamadaY₁ d hNH h561 h562 h591 h592 h593 hx hy
  have h34 := h.inf_normalizer_le_and_le_normalizer d hNH h561 h562 le_sup_right
    (h.yamadaW₁_le_yamadaF₁ d h561 h562) (yamadaF₁_le_yamadaD₁ d) hW₁5 hF₁5
    fun x hx y hy => h.commutatorElement_mem_yamadaW₁ d hNH h561 h562 h591 h592 h593 hx hy
  refine ⟨⟨hcrossed (yamadaW₁_le_yamadaD₁ d) hW₁5, fun w hw =>
      h.exists_mem_inf_normalizer_conj_eq d hNH h561 h562 h591 h592 h593 le_sup_right
        (yamadaW₁_le_yamadaD₁ d) hW₁5 hw⟩,
    ⟨hcrossed (yamadaF₁_le_yamadaD₁ d) hF₁5, fun w hw =>
      h.exists_mem_inf_normalizer_conj_eq d hNH h561 h562 h591 h592 h593 h562.2.2.2
        (yamadaF₁_le_yamadaD₁ d) hF₁5 hw⟩, hR₂, ?_, h34, inf_le_left, ?_⟩
  · rw [hR₂]
    exact h23
  · intro g hg
    refine mem_normalizer_fintype fun x hx => ?_
    have hiff := fun {z : G} => h.mem_inf_normalizer_iff d hNH h561 h562
      (yamadaF₁_le_yamadaD₁ d) hF₁5 (x := z)
    obtain ⟨hx5, hκx⟩ := hiff.1 hx
    exact hiff.2 ⟨mul_mem (mul_mem hg hx5) (inv_mem hg), h.crossed_conj_mem d hNH h561 h562
      h562.2.2.2 (yamadaF₁_le_yamadaD₁ d) hF₁5
      (fun x hx y hy => h.commutatorElement_mem_yamadaF₁ d hNH h561 h562 h591 h592 h593 hx hy)
      hg (h.crossed_mem_yamadaD₁ d hNH h561 h562 (h.yamadaR₅_le_normalizer_yamadaC₁ d hg))
      hx5 hκx⟩

omit [Finite G] in
include h593 in
theorem commutatorElement_mem_yamadaV₁_of_mem_yamadaS₂ {a s : G} (ha : a ∈ yamadaY₂ d t)
    (hs : s ∈ yamadaS₂ d t) : a * s * a⁻¹ * s⁻¹ ∈ yamadaV₁ d t := by
  rw [← h593.2] at ha
  obtain ⟨a', ha', rfl⟩ := ha
  have h1 := (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).1 ha' ⟨s, hs⟩
  rw [← h593.1]
  exact ⟨_, h1, rfl⟩

include h h561 h562 h591 h593 in
theorem yamadaR₂_le_normalizer_yamadaS₁_inf :
    yamadaR₂ d t ≤ normalizer (yamadaS₁ d t : Set G) ⊓ normalizer (yamadaM₁ d t : Set G) := by
  have hSD₁ : d.S.map L.subtype ≤ normalizer (yamadaD₁ d t : Set G) := fun s hs => by
    obtain ⟨s', hs', rfl⟩ := hs
    exact h561.2.2 ⟨s', d.S_le_normalizer_V hs', rfl⟩
  have hgen : ∀ g : G, g ∈ normalizer (yamadaS₁ d t : Set G) →
      g ∈ normalizer (yamadaL₂ d t : Set G) →
        g ∈ normalizer (yamadaS₁ d t : Set G) ⊓ normalizer (yamadaM₁ d t : Set G) :=
    fun g hS hL => mem_inf.2 ⟨hS, Common.mem_normalizer_inf hL hS⟩
  have htL₂ : t ∈ yamadaL₂ d t :=
    h.tM_le_yamadaL₂ d (mem_sup_right (mem_zpowers t))
  rw [h591.2.2.1]
  refine sup_le (sup_le (fun s hs => hgen s (Common.mem_normalizer_sup (le_normalizer hs)
    (hSD₁ hs)) (le_normalizer_yamadaL₂ d t (h.S_le_normalizer_tY d hs))) (fun a ha => ?_))
    ((zpowers_le).2 (hgen t (Common.mem_normalizer_sup (h.t_mem_normalizer_map d.S)
      (h.t_mem_normalizer_yamadaD₁ d)) (le_normalizer htL₂)))
  have haQ := h.yamadaY₂_le_yamadaQ₅ d h561 h562 h591 h593 ha
  have haD₁ := (mem_yamadaQ₅.1 haQ).1.2
  refine hgen a (mem_normalizer_fintype fun z hz => ?_)
    (le_normalizer (yamadaY₂_le_yamadaL₂ d h591 ha))
  have hle : yamadaS₁ d t ≤ (yamadaS₁ d t).comap (MulAut.conj a).toMonoidHom := by
    refine sup_le (fun s hs => ?_) (fun δ hδ => mem_sup_right ((mem_normalizer_iff.1 haD₁ δ).1 hδ))
    have h1 := commutatorElement_mem_yamadaV₁_of_mem_yamadaS₂ d h593 ha (mem_sup_left hs)
    show a * s * a⁻¹ ∈ yamadaS₁ d t
    rw [show a * s * a⁻¹ = a * s * a⁻¹ * s⁻¹ * s by group]
    exact mul_mem (mem_sup_right (yamadaV₁_le_yamadaD₁ d t h1)) (mem_sup_left hs)
  exact hle hz

include h in
theorem yamadaS₁_sup_yamadaC₁ : yamadaS₁ d t ⊔ yamadaC₁ d t = yamadaR₁ d t :=
  le_antisymm (sup_le (sup_le le_sup_right ((h.yamadaD₁_le_yamadaC₁ d).trans le_sup_left))
    le_sup_left) (sup_le le_sup_right (le_sup_left.trans le_sup_left))

include h in
theorem yamadaM₁_sup_yamadaC₁ : yamadaM₁ d t ⊔ yamadaC₁ d t = yamadaR₁ d t := by
  refine le_antisymm (sup_le (inf_le_right.trans ((h.yamadaS₁_sup_yamadaC₁ d) ▸ le_sup_left))
    le_sup_left) (sup_le le_sup_right ?_)
  rw [d.S_eq_sup, Subgroup.map_sup]
  refine sup_le (fun u hu => mem_sup_left ⟨?_, ?_⟩)
    ((D_le_yamadaD₁ d t).trans ((h.yamadaD₁_le_yamadaC₁ d).trans le_sup_right))
  · obtain ⟨u', hu', rfl⟩ := hu
    exact h.tM_le_yamadaL₂ d (mem_sup_left ⟨u', d.U₁_le_M hu', rfl⟩)
  · obtain ⟨u', hu', rfl⟩ := hu
    exact mem_sup_left ⟨u', d.U₁_le_S hu', rfl⟩

include h hNH h561 h562 h591 h592 h593 in
theorem yamadaR₅_inf_normalizer_yamadaR₁_le :
    yamadaR₅ d t ⊓ normalizer (yamadaR₁ d t : Set G) ≤ yamadaR₂ d t := by
  have hCQ := h.yamadaC₅_eq_yamadaQ₅ d hNH h561 h562 h591 h592 h593
  intro x hx
  obtain ⟨hx5, hxN⟩ := mem_inf.1 hx
  rw [← SetLike.mem_coe, h.coe_yamadaR₅ d, Set.mem_mul] at hx5
  obtain ⟨c, hc, s₀, hs₀, rfl⟩ := hx5
  have hcN : c ∈ normalizer (yamadaR₁ d t : Set G) := by
    have := mul_mem hxN (inv_mem (le_normalizer (mem_sup_right hs₀ : s₀ ∈ yamadaR₁ d t)))
    rwa [mul_inv_cancel_right] at this
  have hcQ : c ∈ yamadaQ₅ d t := hCQ ▸ hc
  have hcNC₁ : c ∈ normalizer (yamadaC₁ d t : Set G) := (mem_yamadaQ₅.1 hcQ).1.1
  have hR₁ : ((yamadaR₁ d t : Subgroup G) : Set G) =
      (yamadaC₁ d t : Set G) * ((d.S.map L.subtype : Subgroup G) : Set G) :=
    coe_mul_of_right_le_normalizer_left _ _ (h.S_le_normalizer_yamadaC₁ d)
  have hcomm : ∀ s ∈ d.S.map L.subtype,
      (t * c * t * c⁻¹) * s * (t * c * t * c⁻¹)⁻¹ * s⁻¹ ∈ yamadaV₁ d t := by
    intro s hs
    have hsN : s ∈ normalizer (yamadaC₁ d t : Set G) := h.S_le_normalizer_yamadaC₁ d hs
    have hsC₅ : s ∈ normalizer (yamadaC₅ d t : Set G) := le_normalizer_yamadaC₅ d t hsN
    have hst : s * t = t * s := mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs)
    have hzR₁ : c * s * c⁻¹ * s⁻¹ ∈ yamadaR₁ d t :=
      mul_mem ((mem_normalizer_iff.1 hcN s).1 (mem_sup_right hs)) (inv_mem (mem_sup_right hs))
    have hzC₅ : c * s * c⁻¹ * s⁻¹ ∈ yamadaC₅ d t := by
      rw [show c * s * c⁻¹ * s⁻¹ = c * (s * c⁻¹ * s⁻¹) by group]
      exact mul_mem hc ((mem_normalizer_iff.1 hsC₅ _).1 (inv_mem hc))
    have hzC₁ : c * s * c⁻¹ * s⁻¹ ∈ yamadaC₁ d t := by
      have hz := hzR₁
      rw [← SetLike.mem_coe, hR₁, Set.mem_mul] at hz
      obtain ⟨c₁, hc₁, s', hs', e⟩ := hz
      have hs'C₅ : s' ∈ yamadaC₅ d t := by
        have := mul_mem (inv_mem (yamadaC₁_le_yamadaC₅ d t hc₁)) hzC₅
        rwa [← e, inv_mul_cancel_left] at this
      have hs'C₁ : s' ∈ yamadaC₁ d t := by
        refine h.mem_yamadaC₁_of_crossed_mem d hNH h561 h562 (hCQ ▸ hs'C₅) ?_
        have hs't : s' * t = t * s' := mem_centralizer_singleton_iff.1 (h.S_le_centralizer d hs')
        rw [mul_assoc t s' t, hs't, ← mul_assoc, h.t_mul_t, one_mul, mul_inv_cancel]
        exact one_mem _
      rw [← e]
      exact mul_mem hc₁ hs'C₁
    have hκz : t * (c * s * c⁻¹ * s⁻¹) * t * (c * s * c⁻¹ * s⁻¹)⁻¹ ∈ yamadaV₁ d t := by
      have hmem : (c * s * c⁻¹ * s⁻¹) * t * (c * s * c⁻¹ * s⁻¹)⁻¹ ∈
          {z | ∃ c' ∈ yamadaC₁ d t, c' * t * c'⁻¹ = z} := ⟨_, hzC₁, rfl⟩
      rw [(h.yamada_5_3_1_all d).2.2.2.2.1] at hmem
      obtain ⟨v₀, hv₀, e⟩ := hmem
      rw [show t * (c * s * c⁻¹ * s⁻¹) * t * (c * s * c⁻¹ * s⁻¹)⁻¹ =
        t * ((c * s * c⁻¹ * s⁻¹) * t * (c * s * c⁻¹ * s⁻¹)⁻¹) by group, ← e, ← mul_assoc,
        h.t_mul_t, one_mul]
      exact V_le_yamadaV₁ d h562 hv₀
    have hyN : s * c⁻¹ * s⁻¹ ∈ normalizer (yamadaC₁ d t : Set G) :=
      mul_mem (mul_mem hsN (inv_mem hcNC₁)) (inv_mem hsN)
    have h1 := h.crossed_mul_mem d hNH h561 h562 hcQ hyN
    rw [show c * (s * c⁻¹ * s⁻¹) = c * s * c⁻¹ * s⁻¹ by group] at h1
    have hcy : (t * c * t * c⁻¹) * (t * (s * c⁻¹ * s⁻¹) * t * (s * c⁻¹ * s⁻¹)⁻¹) ∈
        yamadaV₁ d t := by
      have := mul_mem h1 (inv_mem hκz)
      rw [mul_inv_cancel_right] at this
      exact (inv_mem_iff).1 this
    have hst' : s⁻¹ * t = t * s⁻¹ := by
      calc s⁻¹ * t = s⁻¹ * (t * s) * s⁻¹ := by group
        _ = s⁻¹ * (s * t) * s⁻¹ := by rw [hst]
        _ = t * s⁻¹ := by group
    have hκy : t * (s * c⁻¹ * s⁻¹) * t * (s * c⁻¹ * s⁻¹)⁻¹ =
        s * (t * c⁻¹ * t * c⁻¹⁻¹) * s⁻¹ := by
      calc t * (s * c⁻¹ * s⁻¹) * t * (s * c⁻¹ * s⁻¹)⁻¹ =
          (t * s) * c⁻¹ * (s⁻¹ * t) * s * c * s⁻¹ := by group
        _ = (s * t) * c⁻¹ * (t * s⁻¹) * s * c * s⁻¹ := by rw [← hst, hst']
        _ = s * (t * c⁻¹ * t * c⁻¹⁻¹) * s⁻¹ := by group
    rw [hκy] at hcy
    have h2 := h.crossed_mul_mem d hNH h561 h562 hcQ (inv_mem hcNC₁)
    have hκ1 : t * (c * c⁻¹) * t * (c * c⁻¹)⁻¹ = 1 := by
      rw [mul_inv_cancel, mul_one, inv_one, mul_one, h.t_mul_t]
    rw [hκ1, mul_one] at h2
    have hsV : s ∈ normalizer (yamadaV₁ d t : Set G) := S_le_normalizer_yamadaV₁ d h593 hs
    have e : (t * c * t * c⁻¹) * s * (t * c * t * c⁻¹)⁻¹ * s⁻¹ =
        ((t * c * t * c⁻¹) * (s * (t * c⁻¹ * t * c⁻¹⁻¹) * s⁻¹)) *
          (s * ((t * c * t * c⁻¹) * (t * c⁻¹ * t * c⁻¹⁻¹))⁻¹ * s⁻¹) := by group
    rw [e]
    exact mul_mem hcy ((mem_normalizer_iff.1 hsV _).1 h2)
  obtain ⟨n, hn, v, hv, hnv⟩ := h.exists_mul_of_mem_yamadaD₁ d h561 h562
    (h.crossed_mem_yamadaD₁ d hNH h561 h562 hcNC₁)
  have hnY : n ∈ d.Y.map L.subtype := by
    obtain ⟨n', hn', rfl⟩ := hn
    refine ⟨n', d.mem_Y_iff_forall.2 ⟨d.D_le_S hn', fun y hy => ?_⟩, rfl⟩
    have h1 := hcomm (y : G) ⟨y, hy, rfl⟩
    rw [hnv] at h1
    have hvy : (y : G) * v = v * y := mul_comm_of_mem_S_of_mem_yamadaV₁ d h593 ⟨y, hy, rfl⟩ hv
    have e : L.subtype n' * v * y * (L.subtype n' * v)⁻¹ * (y : G)⁻¹ =
        (n' : G) * y * (n' : G)⁻¹ * (y : G)⁻¹ := by
      calc L.subtype n' * v * y * (L.subtype n' * v)⁻¹ * (y : G)⁻¹ =
          (n' : G) * (v * y * v⁻¹) * (n' : G)⁻¹ * (y : G)⁻¹ := by
            simp only [coe_subtype]; group
        _ = (n' : G) * y * (n' : G)⁻¹ * (y : G)⁻¹ := by
            rw [show v * (y : G) * v⁻¹ = y by rw [← hvy, mul_inv_cancel_right]]
    rw [e] at h1
    have h2L : n' * y * n'⁻¹ * y⁻¹ ∈ d.D := by
      rw [show n' * y * n'⁻¹ * y⁻¹ = n' * (y * n'⁻¹ * y⁻¹) by group]
      exact mul_mem hn' ((mem_normalizer_iff.1 (d.S_le_normalizer_D hy) _).1 (inv_mem hn'))
    have hcoe : ((n' * y * n'⁻¹ * y⁻¹ : L) : G) = (n' : G) * y * (n' : G)⁻¹ * (y : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have h3 : ((n' * y * n'⁻¹ * y⁻¹ : L) : G) ∈ d.V.map L.subtype := by
      rw [← h.yamadaV₁_inf_D d h562]
      exact mem_inf.2 ⟨hcoe ▸ h1, ⟨_, h2L, rfl⟩⟩
    rw [commutatorElement_def]
    exact coe_mem_map_subtype_iff_D4.1 h3
  have hκY₁ : t * c * t * c⁻¹ ∈ yamadaY₁ d t := by
    rw [hnv]
    exact mul_mem (mem_sup_left hnY) (mem_sup_right hv)
  have hcR₂ : c ∈ yamadaR₂ d t := by
    rw [h.yamadaR₂_eq_inf_normalizer d hNH h561 h562 h591 h592 h593]
    exact (h.mem_inf_normalizer_iff d hNH h561 h562 (yamadaY₁_le_yamadaD₁ d)
      (h.yamadaR₅_le_normalizer_yamadaY₁ d hNH h561 h562 h591 h592 h593)).2
        ⟨mem_sup_left hc, hκY₁⟩
  exact mul_mem hcR₂ (mem_sup_right hs₀)

include h hNH h561 h562 h591 h592 h593 in
theorem yamada_5_15 :
    yamadaR₅ d t ⊓ normalizer (yamadaS₁ d t : Set G) = yamadaR₂ d t ∧
      yamadaR₅ d t ⊓ normalizer (yamadaM₁ d t : Set G) = yamadaR₂ d t := by
  have hR₂5 := h.yamadaR₂_le_yamadaR₅ d hNH h561 h562 h591 h592 h593
  have hR₂N := h.yamadaR₂_le_normalizer_yamadaS₁_inf d h561 h562 h591 h593
  have hR₁ := h.yamadaR₅_inf_normalizer_yamadaR₁_le d hNH h561 h562 h591 h592 h593
  have hstep : ∀ {X : Subgroup G}, X ⊔ yamadaC₁ d t = yamadaR₁ d t →
      yamadaR₅ d t ⊓ normalizer (X : Set G) ≤ yamadaR₂ d t := fun hX x hx => by
    obtain ⟨hx5, hxX⟩ := mem_inf.1 hx
    refine hR₁ (mem_inf.2 ⟨hx5, ?_⟩)
    rw [← hX]
    exact Common.mem_normalizer_sup hxX (h.yamadaR₅_le_normalizer_yamadaC₁ d hx5)
  exact ⟨le_antisymm (hstep (h.yamadaS₁_sup_yamadaC₁ d))
      (le_inf hR₂5 (hR₂N.trans inf_le_left)),
    le_antisymm (hstep (h.yamadaM₁_sup_yamadaC₁ d)) (le_inf hR₂5 (hR₂N.trans inf_le_right))⟩

end Main

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
