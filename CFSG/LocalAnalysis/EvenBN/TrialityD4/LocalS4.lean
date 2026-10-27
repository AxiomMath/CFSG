module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL3Five
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Nine
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Ten

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open scoped commutatorElement Pointwise

section Generic

variable {G : Type*} [Group G]

private theorem hall_witt_S4 (a b c : G) :
    b * ⁅⁅b⁻¹, a⁆, c⁆ * b⁻¹ * (c * ⁅⁅c⁻¹, b⁆, a⁆ * c⁻¹) * (a * ⁅⁅a⁻¹, c⁆, b⁆ * a⁻¹) = 1 := by
  simp only [commutatorElement_def]
  group

private theorem commutator_commutator_eq_one_S4 {x m w : G} (h₁ : ⁅⁅m⁻¹, w⁆, x⁻¹⁆ = 1)
    (h₂ : ⁅⁅w⁻¹, x⁻¹⁆, m⁆ = 1) : ⁅⁅x, m⁆, w⁆ = 1 := by
  have h := hall_witt_S4 m x⁻¹ w
  rw [inv_inv, h₁, h₂] at h
  have h3 : x⁻¹ * ⁅⁅x, m⁆, w⁆ * x = 1 := by simpa using h
  calc ⁅⁅x, m⁆, w⁆ = x * (x⁻¹ * ⁅⁅x, m⁆, w⁆ * x) * x⁻¹ := by group
    _ = 1 := by rw [h3]; group

private theorem commutator_mul_right_S4 (x s f : G) :
    x * (s * f) * x⁻¹ * (s * f)⁻¹ = (x * s * x⁻¹ * s⁻¹) * (s * (x * f * x⁻¹ * f⁻¹) * s⁻¹) := by
  group

private theorem commutator_mul_mem_S4 {N : Subgroup G} {a b f f' : G}
    (ha : a ∈ normalizer (N : Set G)) (hb : b ∈ normalizer (N : Set G)) (hf : f ∈ N)
    (hf' : f' ∈ N) (hab : a * b * a⁻¹ * b⁻¹ ∈ N) :
    (a * f) * (b * f') * (a * f)⁻¹ * (b * f')⁻¹ ∈ N := by
  have h1 : b⁻¹ * f * b ∈ N := by
    have := (mem_normalizer_iff.1 (inv_mem hb) f).1 hf
    rwa [inv_inv] at this
  have h2 : a * (b⁻¹ * f * b * f' * f⁻¹) * a⁻¹ ∈ N :=
    (mem_normalizer_iff.1 ha _).1 (mul_mem (mul_mem h1 hf') (inv_mem hf))
  have h3 : b * (a * (b⁻¹ * f * b * f' * f⁻¹) * a⁻¹ * f'⁻¹) * b⁻¹ ∈ N :=
    (mem_normalizer_iff.1 hb _).1 (mul_mem h2 (inv_mem hf'))
  have e : (a * f) * (b * f') * (a * f)⁻¹ * (b * f')⁻¹ =
      (a * b * a⁻¹ * b⁻¹) * (b * (a * (b⁻¹ * f * b * f' * f⁻¹) * a⁻¹ * f'⁻¹) * b⁻¹) := by group
  rw [e]
  exact mul_mem hab h3

private theorem mul_self_mul_mem_S4 {N : Subgroup G} {a f : G} (ha : a ∈ normalizer (N : Set G))
    (hf : f ∈ N) (haa : a * a ∈ N) : (a * f) * (a * f) ∈ N := by
  have h1 : a⁻¹ * f * a ∈ N := by
    have := (mem_normalizer_iff.1 (inv_mem ha) f).1 hf
    rwa [inv_inv] at this
  have e : (a * f) * (a * f) = (a * a) * (a⁻¹ * f * a) * f := by group
  rw [e]
  exact mul_mem (mul_mem haa h1) hf

end Generic

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

private theorem mul_self_mem_F_of_mem_S_S4 {s : X} (hs : s ∈ d.S) : s * s ∈ d.F := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff.1 hs
  obtain ⟨b, n', hn', rfl⟩ := d.mem_D_iff.1 hn
  have hu : d.x₁ a ∈ d.S := d.U₁_le_S (d.x₁_mem_U₁ a)
  have hv : d.x₂ b ∈ d.S := d.D_le_S (d.x₂_mem_D b)
  have h₀ : d.x₁ a * d.x₂ b * (d.x₁ a * d.x₂ b) ∈ d.F := by
    have e : d.x₁ a * d.x₂ b * (d.x₁ a * d.x₂ b) = ⁅d.x₁ a, d.x₂ b⁆ := by
      rw [commutatorElement_def, d.x₁_inv, d.x₂_inv]
      group
    rw [e]
    exact d.commutator_S_S (commutator_mem_commutator hu hv)
  have e : d.x₁ a * (d.x₂ b * n') * (d.x₁ a * (d.x₂ b * n')) =
      (d.x₁ a * d.x₂ b * n') * (d.x₁ a * d.x₂ b * n') := by group
  rw [e]
  exact mul_self_mul_mem_S4 (d.S_le_normalizer_F (mul_mem hu hv)) hn' h₀

end TrialityD4Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

private structure Facts (d : TrialityD4Data L (2 ^ f)) (t : G) : Prop where
  t_mem_R₄ : t ∈ yamadaR₄ d t
  S_le_R₄ : d.S.map L.subtype ≤ yamadaR₄ d t
  R₃_le_R₄ : yamadaR₃ d t ≤ yamadaR₄ d t
  R₄_eq : yamadaR₄ d t = yamadaL₄ d t ⊔ yamadaR₃ d t
  R₃_eq : yamadaR₃ d t = yamadaL₃ d t ⊔ d.S.map L.subtype
  L₃_le_L₄ : yamadaL₃ d t ≤ yamadaL₄ d t
  L₄_eq : yamadaL₄ d t = yamadaM₄ d t ⊔ zpowers t
  R₄_le_N_L₄ : yamadaR₄ d t ≤ normalizer (yamadaL₄ d t : Set G)
  R₄_le_N_Y₂ : yamadaR₄ d t ≤ normalizer (yamadaY₂ d t : Set G)
  R₄_le_N_C₅ : yamadaR₄ d t ≤ normalizer (yamadaC₅ d t : Set G)
  R₄_le_N_V₁ : yamadaR₄ d t ≤ normalizer (yamadaV₁ d t : Set G)
  S_le_N_L₃ : d.S.map L.subtype ≤ normalizer (yamadaL₃ d t : Set G)
  S_le_N_W₃ : d.S.map L.subtype ≤ normalizer (yamadaW₃ d t : Set G)
  S_le_N_C₅ : d.S.map L.subtype ≤ normalizer (yamadaC₅ d t : Set G)
  t_not_mem_C_V₁ : t ∉ centralizer (yamadaV₁ d t : Set G)
  S_le_C_V₁ : d.S.map L.subtype ≤ centralizer (yamadaV₁ d t : Set G)
  M_le_C_Y₂ : d.M.map L.subtype ≤ centralizer (yamadaY₂ d t : Set G)
  D_le_C₅ : d.D.map L.subtype ≤ yamadaC₅ d t
  C₅_inf_S : yamadaC₅ d t ⊓ d.S.map L.subtype = d.D.map L.subtype
  L₃_inf_S : yamadaL₃ d t ⊓ d.S.map L.subtype = d.M.map L.subtype
  comm_D₅ : ∀ x ∈ yamadaD₅ d t, ∀ y ∈ yamadaD₅ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaV₁ d t
  sq_D₅ : ∀ x ∈ yamadaD₅ d t, x * x ∈ yamadaV₁ d t
  V₁_le_W₃ : yamadaV₁ d t ≤ yamadaW₃ d t
  Y_le_Y₂ : d.Y.map L.subtype ≤ yamadaY₂ d t
  comm_R₄_le_L₃ : ⁅yamadaR₄ d t, yamadaR₄ d t⁆ ≤ yamadaL₃ d t
  t_not_mem_M₄ : t ∉ yamadaM₄ d t
  L₄_inf_R₃ : yamadaL₄ d t ⊓ yamadaR₃ d t = yamadaL₃ d t
  D₃_eq : yamadaD₃ d t = yamadaW₃ d t ⊔ yamadaD₁ d t
  D₃_le_N_W₃ : yamadaD₃ d t ≤ normalizer (yamadaW₃ d t : Set G)
  D₁_le_D₃ : yamadaD₁ d t ≤ yamadaD₃ d t
  F₃_inf_D₁ : yamadaF₃ d t ⊓ yamadaD₁ d t ≤ yamadaF₁ d t
  W₃_le_F₃ : yamadaW₃ d t ≤ yamadaF₃ d t
  F₁_eq : yamadaF₁ d t = d.F.map L.subtype ⊔ yamadaV₁ d t
  W₁_le_F₁ : yamadaW₁ d t ≤ yamadaF₁ d t
  F₁_le_N_W₁ : yamadaF₁ d t ≤ normalizer (yamadaW₁ d t : Set G)
  crossed_F₁ : ∀ x ∈ yamadaR₄ d t, t * x * t * x⁻¹ ∈ yamadaF₁ d t
  crossed_mul : ∀ x ∈ yamadaR₄ d t, ∀ y ∈ yamadaR₄ d t, ∃ w ∈ yamadaW₁ d t,
    t * (x * y) * t * (x * y)⁻¹ = (t * x * t * x⁻¹) * (t * y * t * y⁻¹) * w
  mem_R₃_iff : ∀ x ∈ yamadaR₄ d t, (x ∈ yamadaR₃ d t ↔ t * x * t * x⁻¹ ∈ yamadaW₁ d t)
  exists_R₄ : ∀ w ∈ yamadaF₁ d t, ∃ x ∈ yamadaR₄ d t, ∃ v ∈ yamadaV₁ d t,
    x * t * x⁻¹ = t * w * v
  card_R₃ : Nat.card (yamadaR₃ d t) = 2 * (2 ^ f) ^ 17
  card_L₃ : Nat.card (yamadaL₃ d t) = 2 * (2 ^ f) ^ 16
  V₁_inf_D : yamadaV₁ d t ⊓ d.D.map L.subtype = d.V.map L.subtype
  card_V₁ : Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2

private theorem facts (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    Facts d t := by
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
  have h521 := h.yamada_5_21 d hlay
  have h514 := h.yamada_5_14 d hNH h561 h562 h591 h592 h593
  have h524 := h.yamada_5_24 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221
  have h525 := h.yamada_5_25 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521
  have h5172 := (h.yamada_5_17_2 d hNH h561 h562 h591 h592 h593 h5101 h5102).2
  have hR₃R₄ : yamadaR₃ d t ≤ yamadaR₄ d t := h514.2.2.2.2.1.1
  have hSR₃ : d.S.map L.subtype ≤ yamadaR₃ d t := h5172 ▸ le_sup_right
  have hF₁R₅ : yamadaF₁ d t ≤ yamadaR₅ d t :=
    ((yamadaF₁_le_yamadaD₁ d).trans ((h.yamadaD₁_le_yamadaC₁ d).trans
      (yamadaC₁_le_yamadaC₅ d t))).trans le_sup_left
  have hR₄V₁ : yamadaR₄ d t ≤ normalizer (yamadaV₁ d t : Set G) := fun x hx => by
    have hxC₅ : x ∈ normalizer (yamadaC₅ d t : Set G) :=
      (h.yamadaR₅_le_normalizer_yamadaC₅ d) ((inf_le_left : yamadaR₄ d t ≤ yamadaR₅ d t) hx)
    have h1 := normalizer_le_normalizer_commutator_C8 (yamadaC₅ d t) hxC₅
    rw [h525.2.1] at h1
    exact normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t h1
  exact
    { t_mem_R₄ := h.t_mem_yamadaR₄ d hNH h561 h562 h591 h592 h593
      S_le_R₄ := hSR₃.trans hR₃R₄
      R₃_le_R₄ := hR₃R₄
      R₄_eq := h524.2.1.1
      R₃_eq := h5172
      L₃_le_L₄ := h524.2.1.2.1.symm.le.trans inf_le_left
      L₄_eq := h524.1.1
      R₄_le_N_L₄ := h524.2.1.2.2.1
      R₄_le_N_Y₂ := h.yamadaR₄_le_normalizer_yamadaY₂ d hNH h561 h562 h591 h592 h593 h5221
      R₄_le_N_C₅ := (inf_le_left : yamadaR₄ d t ≤ yamadaR₅ d t).trans
        (h.yamadaR₅_le_normalizer_yamadaC₅ d)
      R₄_le_N_V₁ := hR₄V₁
      S_le_N_L₃ := h.S_le_normalizer_yamadaL₃ d
      S_le_N_W₃ := fun s hs => (Subgroup.mem_inf.1 (h.S_map_le_normalizer_yamadaW₃ d hlay hs)).2
      S_le_N_C₅ := (h.S_le_normalizer_yamadaC₁ d).trans (le_normalizer_yamadaC₅ d t)
      t_not_mem_C_V₁ := h.t_not_mem_centralizer_yamadaV₁_C8 d h592
      S_le_C_V₁ := fun s hs => mem_centralizer_iff.2 fun v hv =>
        (mul_comm_of_mem_S_of_mem_yamadaV₁ d h593 hs hv).symm
      M_le_C_Y₂ := fun m hm => mem_centralizer_iff.2 fun y hy =>
        (commute_of_mem_M_of_mem_yamadaY₂ d h592 hm hy).symm
      D_le_C₅ := (h.D_map_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t)
      C₅_inf_S := h.yamadaC₅_inf_S_map d hlay
      L₃_inf_S := h.yamadaL₃_inf_S_map d hlay
      comm_D₅ := fun x hx y hy => by
        have := commutator_mem_commutator hx hy
        rwa [h525.1, commutatorElement_def] at this
      sq_D₅ := fun x hx => h.mul_self_mem_yamadaV₁_of_mem_yamadaD₅ d hNH h561 h562 h591 h592 h593
        h5101 h5102 h59e h520 h5221 h521 hx
      V₁_le_W₃ := h.yamadaV₁_le_yamadaW₃_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102
      Y_le_Y₂ := Y_le_yamadaY₂ d h592
      comm_R₄_le_L₃ := h.commutator_yamadaR₄_le_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101 h5102
        h59e h520 h5221
      t_not_mem_M₄ := h524.1.2
      L₄_inf_R₃ := h524.2.1.2.1
      D₃_eq := h.yamadaD₃_eq_sup_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102 h521
      D₃_le_N_W₃ := (le_inf inf_le_right (inf_le_left.trans inf_le_right) :
          yamadaD₃ d t ≤ yamadaD₅ d t).trans
        (h.yamadaD₅_le_normalizer_yamadaW₃ d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520
          h5221 h521).1
      D₁_le_D₃ := h.yamadaD₁_le_yamadaD₃_C9 d hNH h561 h562 h591 h592 h593
      F₃_inf_D₁ := h.yamadaF₃_inf_yamadaD₁_le_C9 d hNH h561 h562 h591 h592 h593 h5101 h5102
      W₃_le_F₃ := h.yamadaW₃_le_yamadaF₃ d hlay
      F₁_eq := h.yamadaF₁_eq_sup d h561 h562
      W₁_le_F₁ := h.yamadaW₁_le_yamadaF₁ d h561 h562
      F₁_le_N_W₁ := hF₁R₅.trans (h.yamadaR₅_le_normalizer_yamadaW₁ d hNH h561 h562 h591 h592 h593)
      crossed_F₁ := fun x hx => h.crossed_mem_yamadaF₁ d hNH h561 h562 h591 h592 h593 hx
      crossed_mul := fun x hx y hy => h.crossed_mul_mem_yamadaW₁ d hNH h561 h562 h591 h592 h593
        ((inf_le_left : yamadaR₄ d t ≤ yamadaR₅ d t) hx)
        (h.crossed_mem_yamadaF₁ d hNH h561 h562 h591 h592 h593 hy)
      mem_R₃_iff := fun x hx => h.mem_yamadaR₃_iff_of_mem_yamadaR₄ d hNH h561 h562 h591 h592 h593 hx
      exists_R₄ := h514.2.1.2
      card_R₃ := h.card_yamadaR₃ d hlay
      card_L₃ := h.card_yamadaL₃ d hlay
      V₁_inf_D := h.yamadaV₁_inf_D d h562
      card_V₁ := h562.2.1 }

section Inclusions

variable (d : TrialityD4Data L (2 ^ f))

private theorem R₄_le_N_M₄ (F : Facts d t) :
    yamadaR₄ d t ≤ normalizer (yamadaM₄ d t : Set G) := fun g hg =>
  mem_normalizer_inf_D4 (le_normalizer hg) (mem_normalizer_centralizer_C8 (F.R₄_le_N_Y₂ hg))

private theorem R₄_le_N_D₄ (F : Facts d t) :
    yamadaR₄ d t ≤ normalizer (yamadaD₄ d t : Set G) := fun g hg =>
  mem_normalizer_inf_D4 (le_normalizer hg) (mem_normalizer_inf_D4 (F.R₄_le_N_C₅ hg)
    (mem_normalizer_centralizer_C8 (F.R₄_le_N_V₁ hg)))

private theorem R₄_le_N_F₄ (F : Facts d t) :
    yamadaR₄ d t ≤ normalizer (yamadaF₄ d t : Set G) := fun g hg =>
  mem_normalizer_inf_D4 (R₄_le_N_M₄ d F hg) (R₄_le_N_D₄ d F hg)

private theorem M_le_M₄ (F : Facts d t) : d.M.map L.subtype ≤ yamadaM₄ d t :=
  le_inf ((map_mono d.M_le_S).trans F.S_le_R₄) F.M_le_C_Y₂

private theorem D_le_D₅ (F : Facts d t) : d.D.map L.subtype ≤ yamadaD₅ d t :=
  le_inf F.D_le_C₅ ((map_mono d.D_le_S).trans F.S_le_C_V₁)

private theorem D_le_D₄ (F : Facts d t) : d.D.map L.subtype ≤ yamadaD₄ d t :=
  le_inf ((map_mono d.D_le_S).trans F.S_le_R₄) (D_le_D₅ d F)

private theorem F_le_F₄ (F : Facts d t) : d.F.map L.subtype ≤ yamadaF₄ d t :=
  le_inf ((map_mono d.F_le_M).trans (M_le_M₄ d F)) ((map_mono d.F_le_D).trans (D_le_D₄ d F))

private theorem S_le_S₄ (F : Facts d t) : d.S.map L.subtype ≤ yamadaS₄ d t :=
  le_inf F.S_le_R₄ F.S_le_C_V₁

private theorem D₄_le_S₄ : yamadaD₄ d t ≤ yamadaS₄ d t :=
  le_inf inf_le_left (inf_le_right.trans inf_le_right)

private theorem F₄_le_D₅ : yamadaF₄ d t ≤ yamadaD₅ d t :=
  (yamadaF₄_le_yamadaD₄ d t).trans inf_le_right

end Inclusions

section Decomposition

private theorem exists_mul_of_mem_S₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (F : Facts d t) {x : G} (hx : x ∈ yamadaS₄ d t) :
    ∃ m ∈ yamadaM₄ d t, ∃ s ∈ d.S.map L.subtype, x = m * s := by
  obtain ⟨hxR₄, hxC⟩ := mem_inf.1 hx
  rw [F.R₄_eq, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _
    (F.R₃_le_R₄.trans F.R₄_le_N_L₄), Set.mem_mul] at hxR₄
  obtain ⟨l, hl, r, hr, rfl⟩ := hxR₄
  rw [F.R₃_eq, coe_mul_of_right_le_normalizer_left _ _ F.S_le_N_L₃, Set.mem_mul] at hr
  obtain ⟨l', hl', s, hs, rfl⟩ := hr
  have hy : l * l' ∈ yamadaM₄ d t ⊔ zpowers t := by
    rw [← F.L₄_eq]
    exact mul_mem (SetLike.mem_coe.1 hl) (F.L₃_le_L₄ (SetLike.mem_coe.1 hl'))
  have hxC' : l * l' * s ∈ centralizer (yamadaV₁ d t : Set G) := by
    rwa [mul_assoc]
  have hsC := F.S_le_C_V₁ hs
  have htM₄ : t ∈ normalizer (yamadaM₄ d t : Set G) :=
    mem_normalizer_inf_D4 (le_normalizer F.t_mem_R₄)
      (mem_normalizer_centralizer_C8 (h.t_mem_normalizer_yamadaY₂ d))
  rw [← mul_assoc]
  rcases (mem_sup_zpowers_iff_of_D4 h.t_mul_t htM₄).1 hy with h1 | ⟨m, hm, e⟩
  · exact ⟨_, h1, s, hs, rfl⟩
  · exfalso
    rw [e] at hxC'
    have hmC : m ∈ centralizer (yamadaV₁ d t : Set G) :=
      centralizer_le (le_sup_left : yamadaV₁ d t ≤ yamadaY₂ d t) (mem_inf.1 hm).2
    have htC : t ∈ centralizer (yamadaV₁ d t : Set G) := by
      have := mul_mem (mul_mem (inv_mem hmC) hxC') (inv_mem hsC)
      rwa [show m⁻¹ * (m * t * s) * s⁻¹ = t by group] at this
    exact F.t_not_mem_C_V₁ htC

private theorem exists_mul_of_mem_M₄ (d : TrialityD4Data L (2 ^ f)) (F : Facts d t) {x : G}
    (hx : x ∈ yamadaM₄ d t) :
    ∃ m ∈ d.M.map L.subtype, ∃ φ ∈ yamadaF₄ d t, x = m * φ := by
  obtain ⟨hxR₄, hxC⟩ := mem_inf.1 hx
  have hxR₅ : x ∈ yamadaC₅ d t ⊔ d.S.map L.subtype :=
    (inf_le_left : yamadaR₄ d t ≤ yamadaR₅ d t) hxR₄
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ F.S_le_N_C₅, Set.mem_mul]
    at hxR₅
  obtain ⟨c, hc, s, hs, rfl⟩ := hxR₅
  obtain ⟨s', hs', rfl⟩ := hs
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff.1 hs'
  have hm₀ : ((d.x₁ a : L) : G) ∈ d.M.map L.subtype := ⟨d.x₁ a, d.x₁_mem_M a, rfl⟩
  have hn₀ : (n : G) ∈ d.D.map L.subtype := ⟨n, hn, rfl⟩
  have hm₀N : ((d.x₁ a : L) : G) ∈ normalizer (yamadaC₅ d t : Set G) :=
    F.S_le_N_C₅ (map_mono d.M_le_S hm₀)
  have hs_eq : L.subtype (d.x₁ a * n) = ((d.x₁ a : L) : G) * (n : G) := rfl
  rw [hs_eq] at hx hxC ⊢
  have hφM : ((d.x₁ a : L) : G)⁻¹ * (c * (((d.x₁ a : L) : G) * (n : G))) ∈ yamadaM₄ d t :=
    mul_mem (inv_mem (M_le_M₄ d F hm₀)) hx
  have hφC₅ : ((d.x₁ a : L) : G)⁻¹ * (c * (((d.x₁ a : L) : G) * (n : G))) ∈ yamadaC₅ d t := by
    have h1 : ((d.x₁ a : L) : G)⁻¹ * c * ((d.x₁ a : L) : G) ∈ yamadaC₅ d t := by
      have := (mem_normalizer_iff.1 (inv_mem hm₀N) c).1 hc
      rwa [inv_inv] at this
    rw [show ((d.x₁ a : L) : G)⁻¹ * (c * (((d.x₁ a : L) : G) * (n : G))) =
      (((d.x₁ a : L) : G)⁻¹ * c * ((d.x₁ a : L) : G)) * (n : G) by group]
    exact mul_mem h1 (F.D_le_C₅ hn₀)
  refine ⟨_, hm₀, _, mem_inf.2 ⟨hφM, mem_inf.2 ⟨(mem_inf.1 hφM).1, mem_inf.2 ⟨hφC₅, ?_⟩⟩⟩,
    by group⟩
  exact centralizer_le (le_sup_left : yamadaV₁ d t ≤ yamadaY₂ d t) (mem_inf.1 hφM).2

private theorem exists_mul_of_mem_S₄' (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (F : Facts d t) {x : G} (hx : x ∈ yamadaS₄ d t) :
    ∃ s ∈ d.S.map L.subtype, ∃ φ ∈ yamadaF₄ d t, x = s * φ := by
  obtain ⟨m, hm, s, hs, rfl⟩ := exists_mul_of_mem_S₄ h d F hx
  obtain ⟨m₁, hm₁, φ, hφ, rfl⟩ := exists_mul_of_mem_M₄ d F hm
  refine ⟨m₁ * s, mul_mem (map_mono d.M_le_S hm₁) hs, s⁻¹ * φ * s, ?_, by group⟩
  have := (mem_normalizer_iff.1 (inv_mem (R₄_le_N_F₄ d F (F.S_le_R₄ hs))) φ).1 hφ
  rwa [inv_inv] at this

end Decomposition

section Commutator

private theorem commutator_M_W_mem_Y (d : TrialityD4Data L (2 ^ f)) {m w : G}
    (hm : m ∈ d.M.map L.subtype) (hw : w ∈ d.W.map L.subtype) :
    m * w * m⁻¹ * w⁻¹ ∈ d.Y.map L.subtype := by
  obtain ⟨m', hm', rfl⟩ := hm
  obtain ⟨w', hw', rfl⟩ := hw
  have h1 : ⁅m', w'⁆ ∈ d.Y := by
    rw [← commutatorElement_inv]
    exact inv_mem ((d.mem_W_iff_forall_M.1 hw').2 m' hm')
  exact ⟨⁅m', w'⁆, h1, map_commutatorElement _ _ _⟩

private theorem commutator_mem_yamadaW₃_of_mem_F₄_M (d : TrialityD4Data L (2 ^ f))
    (F : Facts d t) {x m : G} (hx : x ∈ yamadaF₄ d t) (hm : m ∈ d.M.map L.subtype) :
    x * m * x⁻¹ * m⁻¹ ∈ yamadaW₃ d t := by
  have hxR₄ : x ∈ yamadaR₄ d t := (mem_inf.1 (yamadaF₄_le_yamadaM₄ d t hx)).1
  have hmR₄ : m ∈ yamadaR₄ d t := ((map_mono d.M_le_S).trans F.S_le_R₄) hm
  have hcL₃ : x * m * x⁻¹ * m⁻¹ ∈ yamadaL₃ d t := by
    have := F.comm_R₄_le_L₃ (commutator_mem_commutator hxR₄ hmR₄)
    rwa [commutatorElement_def] at this
  have hxY₂ : x ∈ centralizer (yamadaY₂ d t : Set G) := (mem_inf.1 (yamadaF₄_le_yamadaM₄ d t hx)).2
  have hmY₂ : m ∈ centralizer (yamadaY₂ d t : Set G) := F.M_le_C_Y₂ hm
  have hcY₂ : x * m * x⁻¹ * m⁻¹ ∈ centralizer (yamadaY₂ d t : Set G) :=
    mul_mem (mul_mem (mul_mem hxY₂ hmY₂) (inv_mem hxY₂)) (inv_mem hmY₂)
  have hWD₅ : d.W.map L.subtype ≤ yamadaD₅ d t :=
    ((map_mono (d.W_le_F.trans d.F_le_D)).trans (D_le_D₅ d F))
  have hcW : d.W.map L.subtype ≤ Subgroup.centralizer ({x * m * x⁻¹ * m⁻¹} : Set G) := by
    intro w hw
    rw [mem_centralizer_singleton_iff]
    have h₁ : ⁅⁅m⁻¹, w⁆, x⁻¹⁆ = 1 := by
      have hy : ⁅m⁻¹, w⁆ ∈ yamadaY₂ d t :=
        F.Y_le_Y₂ (by simpa [commutatorElement_def] using commutator_M_W_mem_Y d (inv_mem hm) hw)
      exact commutatorElement_eq_one_iff_mul_comm.2
        (mem_centralizer_iff.1 (inv_mem hxY₂) _ hy)
    have h₂ : ⁅⁅w⁻¹, x⁻¹⁆, m⁆ = 1 := by
      have hv : ⁅w⁻¹, x⁻¹⁆ ∈ yamadaV₁ d t := by
        have := F.comm_D₅ w⁻¹ (inv_mem (hWD₅ hw)) x⁻¹ (inv_mem (F₄_le_D₅ d hx))
        simpa [commutatorElement_def] using this
      exact commutatorElement_eq_one_iff_mul_comm.2
        (mem_centralizer_iff.1 hmY₂ _ (le_sup_left (a := yamadaV₁ d t) hv))
    have h3 := commutator_commutator_eq_one_S4 h₁ h₂
    rw [commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3.symm
  have hcW₂ : x * m * x⁻¹ * m⁻¹ ∈ centralizer (yamadaW₂ d t : Set G) := by
    refine mem_centralizer_iff.2 fun w hw => ?_
    have hle : yamadaW₂ d t ≤ Subgroup.centralizer ({x * m * x⁻¹ * m⁻¹} : Set G) :=
      sup_le hcW fun y hy => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hcY₂ y hy)
    exact mem_centralizer_singleton_iff.1 (hle hw)
  exact mem_inf.2 ⟨hcL₃, hcW₂⟩

private theorem commutator_mem_yamadaW₃_of_mem_F₄_S (d : TrialityD4Data L (2 ^ f))
    (F : Facts d t) {x s : G} (hx : x ∈ yamadaF₄ d t) (hs : s ∈ d.S.map L.subtype) :
    x * s * x⁻¹ * s⁻¹ ∈ yamadaW₃ d t := by
  obtain ⟨s', hs', rfl⟩ := hs
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff.1 hs'
  have hm₀ : ((d.x₁ a : L) : G) ∈ d.M.map L.subtype := ⟨d.x₁ a, d.x₁_mem_M a, rfl⟩
  have hn₀ : (n : G) ∈ d.D.map L.subtype := ⟨n, hn, rfl⟩
  have hs_eq : L.subtype (d.x₁ a * n) = ((d.x₁ a : L) : G) * (n : G) := rfl
  rw [hs_eq, commutator_mul_right_S4]
  refine mul_mem (commutator_mem_yamadaW₃_of_mem_F₄_M d F hx hm₀) ?_
  exact (mem_normalizer_iff.1 (F.S_le_N_W₃ (map_mono d.M_le_S hm₀)) _).1
    (F.V₁_le_W₃ (F.comm_D₅ x (F₄_le_D₅ d hx) n (D_le_D₅ d F hn₀)))

end Commutator

section Statements

theorem yamadaR₄_le_normalizer_yamadaF₄_S4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaR₄ d t ≤ normalizer (yamadaF₄ d t : Set G) :=
  R₄_le_N_F₄ d (facts h d hlay)

theorem yamadaM₄_eq_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaM₄ d t = d.M.map L.subtype ⊔ yamadaF₄ d t := by
  have F := facts h d hlay
  refine le_antisymm (fun x hx => ?_) (sup_le (M_le_M₄ d F) (yamadaF₄_le_yamadaM₄ d t))
  obtain ⟨m, hm, φ, hφ, rfl⟩ := exists_mul_of_mem_M₄ d F hx
  exact mul_mem (mem_sup_left hm) (mem_sup_right hφ)

theorem yamadaD₄_eq_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaD₄ d t = d.D.map L.subtype ⊔ yamadaF₄ d t := by
  have F := facts h d hlay
  refine le_antisymm (fun x hx => ?_) (sup_le (D_le_D₄ d F) (yamadaF₄_le_yamadaD₄ d t))
  obtain ⟨s, hs, φ, hφ, rfl⟩ := exists_mul_of_mem_S₄' h d F (D₄_le_S₄ d hx)
  have hsC₅ : s ∈ yamadaC₅ d t := by
    have h1 := (mem_inf.1 (mem_inf.1 hx).2).1
    have h2 : φ ∈ yamadaC₅ d t := (mem_inf.1 (F₄_le_D₅ d hφ)).1
    have := mul_mem h1 (inv_mem h2)
    rwa [mul_inv_cancel_right] at this
  have hsD : s ∈ d.D.map L.subtype := by
    rw [← F.C₅_inf_S]
    exact mem_inf.2 ⟨hsC₅, hs⟩
  exact mul_mem (mem_sup_left hsD) (mem_sup_right hφ)

theorem yamadaS₄_eq_yamadaF₄_sup_S (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaS₄ d t = yamadaF₄ d t ⊔ d.S.map L.subtype := by
  have F := facts h d hlay
  refine le_antisymm (fun x hx => ?_) (sup_le ((yamadaF₄_le_yamadaD₄ d t).trans (D₄_le_S₄ d))
    (S_le_S₄ d F))
  obtain ⟨s, hs, φ, hφ, rfl⟩ := exists_mul_of_mem_S₄' h d F hx
  rw [sup_comm]
  exact mul_mem (mem_sup_left hs) (mem_sup_right hφ)

theorem S_map_inf_yamadaF₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : d.S.map L.subtype ⊓ yamadaF₄ d t = d.F.map L.subtype := by
  have F := facts h d hlay
  refine le_antisymm (fun x hx => ?_) (le_inf (map_mono d.F_le_S) (F_le_F₄ d F))
  obtain ⟨hxS, hxF⟩ := mem_inf.1 hx
  have hxD : x ∈ d.D.map L.subtype := by
    rw [← F.C₅_inf_S]
    exact mem_inf.2 ⟨(F₄_le_D₅ d hxF |> mem_inf.1).1, hxS⟩
  obtain ⟨s, hs, rfl⟩ := hxS
  have hsM : s ∈ d.M := by
    rw [← d.S_inf_centralizer_Y]
    refine mem_inf.2 ⟨hs, mem_centralizer_iff.2 fun y hy => Subtype.ext ?_⟩
    have hxC : (s : G) ∈ centralizer (yamadaY₂ d t : Set G) :=
      (mem_inf.1 (yamadaF₄_le_yamadaM₄ d t hxF)).2
    exact mem_centralizer_iff.1 hxC (y : G) (F.Y_le_Y₂ ⟨y, hy, rfl⟩)
  have hsD : s ∈ d.D := (mem_map_iff_mem L.subtype_injective).1 hxD
  exact ⟨s, d.M_inf_D_le_F ⟨hsM, hsD⟩, rfl⟩

theorem crossed_mem_yamadaF₄_of_mem_yamadaS₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} (hx : x ∈ yamadaS₄ d t) :
    t * x * t * x⁻¹ ∈ yamadaF₄ d t := by
  have F := facts h d hlay
  obtain ⟨s, hs, φ, hφ, rfl⟩ := exists_mul_of_mem_S₄' h d F hx
  have hst : s * t = t * s := by
    obtain ⟨s', hs', rfl⟩ := hs
    exact mem_centralizer_singleton_iff.1 (h.L_le_centralizer s'.2)
  have htF : t ∈ normalizer (yamadaF₄ d t : Set G) := R₄_le_N_F₄ d F F.t_mem_R₄
  have h1 : t * φ * t * φ⁻¹ ∈ yamadaF₄ d t := by
    have := mul_mem ((mem_normalizer_iff.1 htF φ).1 hφ) (inv_mem hφ)
    rwa [show t * φ * t⁻¹ = t * φ * t by rw [inv_eq_of_mul_eq_one_right h.t_mul_t]] at this
  have h2 := (mem_normalizer_iff.1 (R₄_le_N_F₄ d F (F.S_le_R₄ hs)) _).1 h1
  rwa [show s * (t * φ * t * φ⁻¹) * s⁻¹ = t * (s * φ) * t * (s * φ)⁻¹ by
    calc s * (t * φ * t * φ⁻¹) * s⁻¹ = (s * t) * φ * t * φ⁻¹ * s⁻¹ := by group
      _ = (t * s) * φ * t * φ⁻¹ * s⁻¹ := by rw [hst]
      _ = t * (s * φ) * t * (s * φ)⁻¹ := by group] at h2

theorem commutator_mem_yamadaF₄_of_mem_yamadaS₄ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {x y : G} (hx : x ∈ yamadaS₄ d t)
    (hy : y ∈ yamadaS₄ d t) : x * y * x⁻¹ * y⁻¹ ∈ yamadaF₄ d t := by
  have F := facts h d hlay
  obtain ⟨s, hs, φ, hφ, rfl⟩ := exists_mul_of_mem_S₄' h d F hx
  obtain ⟨s', hs', φ', hφ', rfl⟩ := exists_mul_of_mem_S₄' h d F hy
  refine commutator_mul_mem_S4 (R₄_le_N_F₄ d F (F.S_le_R₄ hs)) (R₄_le_N_F₄ d F (F.S_le_R₄ hs'))
    hφ hφ' ?_
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨b, hb, rfl⟩ := hs'
  exact F_le_F₄ d F ⟨⁅a, b⁆, d.commutator_S_S (commutator_mem_commutator ha hb),
    map_commutatorElement _ _ _⟩

theorem mul_self_mem_yamadaF₄_of_mem_yamadaS₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} (hx : x ∈ yamadaS₄ d t) : x * x ∈ yamadaF₄ d t := by
  have F := facts h d hlay
  obtain ⟨s, hs, φ, hφ, rfl⟩ := exists_mul_of_mem_S₄' h d F hx
  refine mul_self_mul_mem_S4 (R₄_le_N_F₄ d F (F.S_le_R₄ hs)) hφ ?_
  obtain ⟨a, ha, rfl⟩ := hs
  exact F_le_F₄ d F ⟨a * a, d.mul_self_mem_F_of_mem_S_S4 ha, rfl⟩

theorem mul_self_mem_yamadaW₃_of_mem_yamadaF₄_S4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} (hx : x ∈ yamadaF₄ d t) : x * x ∈ yamadaW₃ d t := by
  have F := facts h d hlay
  exact F.V₁_le_W₃ (F.sq_D₅ x (F₄_le_D₅ d hx))

theorem commutator_mem_yamadaW₃_of_mem_yamadaF₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x y : G} (hx : x ∈ yamadaF₄ d t) (hy : y ∈ yamadaS₄ d t) :
    x * y * x⁻¹ * y⁻¹ ∈ yamadaW₃ d t := by
  have F := facts h d hlay
  obtain ⟨s, hs, φ, hφ, rfl⟩ := exists_mul_of_mem_S₄' h d F hy
  rw [commutator_mul_right_S4]
  exact mul_mem (commutator_mem_yamadaW₃_of_mem_F₄_S d F hx hs)
    ((mem_normalizer_iff.1 (F.S_le_N_W₃ hs) _).1
      (F.V₁_le_W₃ (F.comm_D₅ x (F₄_le_D₅ d hx) φ (F₄_le_D₅ d hφ))))

theorem mem_or_mem_of_mul_self_mem_yamadaW₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {s : G} (hs : s ∈ yamadaS₄ d t) (h2 : s * s ∈ yamadaW₃ d t) :
    s ∈ yamadaM₄ d t ∨ s ∈ yamadaD₄ d t := by
  have F := facts h d hlay
  obtain ⟨s₀, hs₀, φ, hφ, rfl⟩ := exists_mul_of_mem_S₄' h d F hs
  have hc : s₀⁻¹ * φ * s₀ * φ⁻¹ ∈ yamadaW₃ d t := by
    have := inv_mem (commutator_mem_yamadaW₃_of_mem_yamadaF₄ h d hlay hφ
      (S_le_S₄ d F (inv_mem hs₀)))
    rwa [show (φ * s₀⁻¹ * φ⁻¹ * s₀⁻¹⁻¹)⁻¹ = s₀⁻¹ * φ * s₀ * φ⁻¹ by group] at this
  have hφφ := mul_self_mem_yamadaW₃_of_mem_yamadaF₄_S4 h d hlay hφ
  have hss : s₀ * s₀ ∈ yamadaW₃ d t := by
    have := mul_mem (mul_mem h2 (inv_mem hφφ)) (inv_mem hc)
    rwa [show s₀ * φ * (s₀ * φ) * (φ * φ)⁻¹ * (s₀⁻¹ * φ * s₀ * φ⁻¹)⁻¹ = s₀ * s₀ by group]
      at this
  obtain ⟨s', hs', rfl⟩ := hs₀
  have h1 : L.subtype (s' * s') ∈ yamadaL₃ d t ⊓ d.S.map L.subtype :=
    mem_inf.2 ⟨(mem_inf.1 hss).1, ⟨s' * s', mul_mem hs' hs', rfl⟩⟩
  rw [F.L₃_inf_S] at h1
  have hM : s' * s' ∈ d.M := (mem_map_iff_mem L.subtype_injective).1 h1
  have hW : s' * s' ∈ d.W := by
    rw [← d.M_inf_centralizer_W_C9]
    refine mem_inf.2 ⟨hM, mem_centralizer_iff.2 fun w hw => Subtype.ext ?_⟩
    exact mem_centralizer_iff.1 (mem_inf.1 hss).2 (w : G)
      (le_sup_left (a := d.W.map L.subtype) (b := yamadaY₂ d t) ⟨w, hw, rfl⟩)
  rcases d.mem_M_or_mem_D_of_mul_self_mem_W hs' hW with hsM | hsD
  · exact Or.inl (mul_mem (M_le_M₄ d F ⟨s', hsM, rfl⟩) (yamadaF₄_le_yamadaM₄ d t hφ))
  · exact Or.inr (mul_mem (D_le_D₄ d F ⟨s', hsD, rfl⟩) (yamadaF₄_le_yamadaD₄ d t hφ))

theorem normalizer_yamadaD₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d)
    (hK : normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaS₄ d t : Set G) ⊓
      normalizer (yamadaW₃ d t : Set G) ⊓ normalizer (yamadaY₂ d t : Set G)) :
    normalizer (yamadaR₄ d t : Set G) ≤
      normalizer (yamadaD₄ d t : Set G) ⊓ normalizer (yamadaF₄ d t : Set G) := by
  have F := facts h d hlay
  intro g hg
  obtain ⟨hgSW, hgY₂⟩ := mem_inf.1 (hK hg)
  obtain ⟨hgS₄, hgW₃⟩ := mem_inf.1 hgSW
  have hgM₄ : g ∈ normalizer (yamadaM₄ d t : Set G) :=
    mem_normalizer_inf_D4 hg (mem_normalizer_centralizer_C8 hgY₂)
  have key : ∀ x ∈ yamadaD₄ d t, g * x * g⁻¹ ∈ yamadaM₄ d t ∨ g * x * g⁻¹ ∈ yamadaD₄ d t := by
    intro x hx
    refine mem_or_mem_of_mul_self_mem_yamadaW₃ h d hlay
      ((mem_normalizer_iff.1 hgS₄ x).1 (D₄_le_S₄ d hx)) ?_
    rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group]
    exact (mem_normalizer_iff.1 hgW₃ _).1 (F.V₁_le_W₃ (F.sq_D₅ x (mem_inf.1 hx).2))
  have hgD₄ : g ∈ normalizer (yamadaD₄ d t : Set G) := by
    rcases le_or_le_of_forall_mem_or_D3
      (H := (yamadaD₄ d t).map (MulAut.conj g).toMonoidHom) (A := yamadaM₄ d t)
      (B := yamadaD₄ d t) (by
        rintro _ ⟨x, hx, rfl⟩
        exact key x hx) with hM | hD
    · exfalso
      have hDM : yamadaD₄ d t ≤ yamadaM₄ d t := fun x hx => by
        have h1 : g * x * g⁻¹ ∈ yamadaM₄ d t := hM ⟨x, hx, rfl⟩
        have := (mem_normalizer_iff.1 (inv_mem hgM₄) _).1 h1
        rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
      refine d.not_D_le_M fun δ hδ => ?_
      rw [← d.S_inf_centralizer_Y]
      refine mem_inf.2 ⟨d.D_le_S hδ, mem_centralizer_iff.2 fun y hy => Subtype.ext ?_⟩
      have hδM₄ : (δ : G) ∈ centralizer (yamadaY₂ d t : Set G) :=
        (mem_inf.1 (hDM (D_le_D₄ d F ⟨δ, hδ, rfl⟩))).2
      exact mem_centralizer_iff.1 hδM₄ (y : G) (F.Y_le_Y₂ ⟨y, hy, rfl⟩)
    · exact mem_normalizer_fintype fun x hx => hD ⟨x, hx, rfl⟩
  exact mem_inf.2 ⟨hgD₄, mem_normalizer_inf_D4 hgM₄ hgD₄⟩

theorem yamadaF₃_eq_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaF₃ d t = yamadaF₁ d t ⊔ yamadaW₃ d t := by
  have F := facts h d hlay
  have hM₃ : d.M.map L.subtype ≤ yamadaM₃ d t :=
    le_inf (F.L₃_inf_S.symm.le.trans inf_le_left) F.M_le_C_Y₂
  have hF₁F₃ : yamadaF₁ d t ≤ yamadaF₃ d t := fun x hx => by
    have hxD₁ : x ∈ yamadaD₁ d t := yamadaF₁_le_yamadaD₁ d hx
    have hxM₃ : x ∈ yamadaM₃ d t := by
      rw [F.F₁_eq] at hx
      exact (sup_le ((map_mono d.F_le_M).trans hM₃)
        (F.V₁_le_W₃.trans (F.W₃_le_F₃.trans inf_le_left)) : _ ≤ yamadaM₃ d t) hx
    exact mem_inf.2 ⟨hxM₃, F.D₁_le_D₃ hxD₁⟩
  refine le_antisymm (fun z hz => ?_) (sup_le hF₁F₃ F.W₃_le_F₃)
  have hzD₃ : z ∈ yamadaD₃ d t := (mem_inf.1 hz).2
  rw [F.D₃_eq, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _
    (F.D₁_le_D₃.trans F.D₃_le_N_W₃), Set.mem_mul] at hzD₃
  obtain ⟨w, hw, d₁, hd₁, rfl⟩ := hzD₃
  have hwF₃ : w ∈ yamadaF₃ d t := F.W₃_le_F₃ (SetLike.mem_coe.1 hw)
  have hd₁F₃ : d₁ ∈ yamadaF₃ d t := by
    have := mul_mem (inv_mem hwF₃) hz
    rwa [inv_mul_cancel_left] at this
  exact mul_mem (mem_sup_right (SetLike.mem_coe.1 hw))
    (mem_sup_left (F.F₃_inf_D₁ (mem_inf.2 ⟨hd₁F₃, SetLike.mem_coe.1 hd₁⟩)))

end Statements

section Orders

private theorem V₁_le_normalizer_S4 (d : TrialityD4Data L (2 ^ f)) (F : Facts d t)
    {A : Subgroup G} (hA : A ≤ d.S.map L.subtype) : yamadaV₁ d t ≤ normalizer (A : Set G) :=
  fun v hv => mem_normalizer_fintype fun a ha => by
    rw [SetLike.mem_coe, mem_centralizer_iff.1 (F.S_le_C_V₁ (hA ha)) v hv, mul_inv_cancel_right]
    exact ha

private theorem V_le_V₁_S4 (d : TrialityD4Data L (2 ^ f)) (F : Facts d t) :
    d.V.map L.subtype ≤ yamadaV₁ d t :=
  F.V₁_inf_D.symm.le.trans inf_le_left

private theorem card_W₁ (d : TrialityD4Data L (2 ^ f)) (F : Facts d t) :
    Nat.card (yamadaW₁ d t) = (2 ^ f) ^ 6 := by
  have hWS : d.W.map L.subtype ≤ d.S.map L.subtype :=
    map_mono (d.W_le_F.trans (d.F_le_D.trans d.D_le_S))
  have h1 := card_sup_mul_card_inf_eq_D4 (A := d.W.map L.subtype) (B := yamadaV₁ d t)
    (V₁_le_normalizer_S4 d F hWS)
  have hinf : d.W.map L.subtype ⊓ yamadaV₁ d t = d.V.map L.subtype := by
    refine le_antisymm (fun x hx => ?_) (le_inf (map_mono (d.V_le_Y.trans d.Y_le_W))
      (V_le_V₁_S4 d F))
    rw [← F.V₁_inf_D]
    exact mem_inf.2 ⟨(mem_inf.1 hx).2, map_mono (d.W_le_F.trans d.F_le_D) (mem_inf.1 hx).1⟩
  rw [hinf, card_map_of_injective L.subtype_injective, card_map_of_injective
    L.subtype_injective, d.card_V, d.card_W, F.card_V₁] at h1
  refine Nat.eq_of_mul_eq_mul_right (m := 2 ^ f) (by positivity) ?_
  calc Nat.card (yamadaW₁ d t) * 2 ^ f = (2 ^ f) ^ 5 * (2 ^ f) ^ 2 := h1
    _ = (2 ^ f) ^ 6 * 2 ^ f := by ring

private theorem card_F₁ (d : TrialityD4Data L (2 ^ f)) (F : Facts d t) :
    Nat.card (yamadaF₁ d t) = (2 ^ f) ^ 9 := by
  have hFS : d.F.map L.subtype ≤ d.S.map L.subtype := map_mono (d.F_le_D.trans d.D_le_S)
  have h1 := card_sup_mul_card_inf_eq_D4 (A := d.F.map L.subtype) (B := yamadaV₁ d t)
    (V₁_le_normalizer_S4 d F hFS)
  have hinf : d.F.map L.subtype ⊓ yamadaV₁ d t = d.V.map L.subtype := by
    refine le_antisymm (fun x hx => ?_) (le_inf (map_mono (d.V_le_Y.trans
      (d.Y_le_W.trans d.W_le_F))) (V_le_V₁_S4 d F))
    rw [← F.V₁_inf_D]
    exact mem_inf.2 ⟨(mem_inf.1 hx).2, map_mono d.F_le_D (mem_inf.1 hx).1⟩
  rw [← F.F₁_eq, hinf, card_map_of_injective L.subtype_injective, card_map_of_injective
    L.subtype_injective, d.card_V, d.card_F, F.card_V₁] at h1
  refine Nat.eq_of_mul_eq_mul_right (m := 2 ^ f) (by positivity) ?_
  calc Nat.card (yamadaF₁ d t) * 2 ^ f = (2 ^ f) ^ 8 * (2 ^ f) ^ 2 := h1
    _ = (2 ^ f) ^ 9 * 2 ^ f := by ring

private theorem relIndex_R₃_R₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (F : Facts d t) : (yamadaR₃ d t).relIndex (yamadaR₄ d t) = (2 ^ f) ^ 3 := by
  haveI hN : ((yamadaW₁ d t).subgroupOf (yamadaF₁ d t)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer F.W₁_le_F₁).2 F.F₁_le_N_W₁
  let κ : yamadaR₄ d t →* yamadaF₁ d t ⧸ (yamadaW₁ d t).subgroupOf (yamadaF₁ d t) :=
    { toFun := fun x => QuotientGroup.mk ⟨t * (x : G) * t * (x : G)⁻¹, F.crossed_F₁ x x.2⟩
      map_one' := by
        refine (QuotientGroup.eq_one_iff _).2 ?_
        rw [Subgroup.mem_subgroupOf]
        show t * ((1 : yamadaR₄ d t) : G) * t * ((1 : yamadaR₄ d t) : G)⁻¹ ∈ yamadaW₁ d t
        simp only [OneMemClass.coe_one, mul_one, inv_one, h.t_mul_t]
        exact one_mem _
      map_mul' := fun x y => by
        obtain ⟨w, hw, e⟩ := F.crossed_mul x x.2 y y.2
        rw [← QuotientGroup.mk_mul]
        refine QuotientGroup.eq.2 ?_
        rw [Subgroup.mem_subgroupOf]
        show (t * ((x : G) * (y : G)) * t * ((x : G) * (y : G))⁻¹)⁻¹ *
          ((t * (x : G) * t * (x : G)⁻¹) * (t * (y : G) * t * (y : G)⁻¹)) ∈ yamadaW₁ d t
        rw [e, show ((t * (x : G) * t * (x : G)⁻¹) * (t * (y : G) * t * (y : G)⁻¹) * w)⁻¹ *
          ((t * (x : G) * t * (x : G)⁻¹) * (t * (y : G) * t * (y : G)⁻¹)) = w⁻¹ by group]
        exact inv_mem hw }
  have hker : κ.ker = (yamadaR₃ d t).subgroupOf (yamadaR₄ d t) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk ⟨t * (x : G) * t * (x : G)⁻¹, F.crossed_F₁ x x.2⟩ :
      yamadaF₁ d t ⧸ (yamadaW₁ d t).subgroupOf (yamadaF₁ d t)) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact (F.mem_R₃_iff x x.2).symm
  have hsurj : Function.Surjective κ := by
    intro q
    obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hx, v, hv, e⟩ := F.exists_R₄ w hw
    refine ⟨⟨x, hx⟩, ?_⟩
    show (QuotientGroup.mk ⟨t * x * t * x⁻¹, F.crossed_F₁ x hx⟩ :
      yamadaF₁ d t ⧸ (yamadaW₁ d t).subgroupOf (yamadaF₁ d t)) = QuotientGroup.mk ⟨w, hw⟩
    refine QuotientGroup.eq.2 ?_
    rw [Subgroup.mem_subgroupOf]
    show (t * x * t * x⁻¹)⁻¹ * w ∈ yamadaW₁ d t
    have e' : t * x * t * x⁻¹ = w * v := by
      rw [show t * x * t * x⁻¹ = t * (x * t * x⁻¹) by group, e, ← mul_assoc, ← mul_assoc,
        h.t_mul_t, one_mul]
    rw [e', show (w * v)⁻¹ * w = v⁻¹ by group]
    exact inv_mem (mem_sup_right hv)
  have h1 := Subgroup.index_ker κ
  rw [hker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top, ← Subgroup.index_eq_card] at h1
  have h3 := Subgroup.relIndex_mul_card (H := yamadaW₁ d t) (K := yamadaF₁ d t)
  rw [inf_eq_left.2 F.W₁_le_F₁, card_W₁ d F, card_F₁ d F] at h3
  have h4 : (yamadaW₁ d t).relIndex (yamadaF₁ d t) = (2 ^ f) ^ 3 := by
    refine Nat.eq_of_mul_eq_mul_right (m := (2 ^ f) ^ 6) (by positivity) ?_
    rw [h3]
    ring
  exact h1.trans h4

theorem card_yamadaR₄_S4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    Nat.card (yamadaR₄ d t) = 2 * (2 ^ f) ^ 20 := by
  have F := facts h d hlay
  have h1 := Subgroup.relIndex_mul_card (H := yamadaR₃ d t) (K := yamadaR₄ d t)
  rw [inf_eq_left.2 F.R₃_le_R₄, F.card_R₃, relIndex_R₃_R₄ h d F] at h1
  rw [← h1]
  ring

theorem card_yamadaL₄_S4 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    Nat.card (yamadaL₄ d t) = 2 * (2 ^ f) ^ 19 := by
  have F := facts h d hlay
  have h1 := card_sup_mul_card_inf_eq_D4 (A := yamadaL₄ d t) (B := yamadaR₃ d t)
    (F.R₃_le_R₄.trans F.R₄_le_N_L₄)
  rw [← F.R₄_eq, F.L₄_inf_R₃, card_yamadaR₄_S4 h d hlay, F.card_L₃, F.card_R₃] at h1
  refine Nat.eq_of_mul_eq_mul_right (m := 2 * (2 ^ f) ^ 17) (by positivity) ?_
  calc Nat.card (yamadaL₄ d t) * (2 * (2 ^ f) ^ 17) = 2 * (2 ^ f) ^ 20 * (2 * (2 ^ f) ^ 16) :=
      h1.symm
    _ = 2 * (2 ^ f) ^ 19 * (2 * (2 ^ f) ^ 17) := by ring

theorem card_yamadaM₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    Nat.card (yamadaM₄ d t) = (2 ^ f) ^ 19 := by
  have F := facts h d hlay
  have htM₄ : t ∈ normalizer (yamadaM₄ d t : Set G) :=
    mem_normalizer_inf_D4 (le_normalizer F.t_mem_R₄)
      (mem_normalizer_centralizer_C8 (h.t_mem_normalizer_yamadaY₂ d))
  have hinf : yamadaM₄ d t ⊓ zpowers t = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxM, hxt⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxt
    rcases h.zpow_eq_one_or_eq k with hk | hk
    · rw [hk]
      exact one_mem _
    · rw [hk] at hxM
      exact absurd hxM F.t_not_mem_M₄
  have h1 := card_sup_mul_card_inf_eq_D4 (A := yamadaM₄ d t) (B := zpowers t)
    ((zpowers_le).2 htM₄)
  rw [← F.L₄_eq, hinf, Subgroup.card_bot, h.card_zpowers_t, card_yamadaL₄_S4 h d hlay] at h1
  omega

theorem card_yamadaF₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    Nat.card (yamadaF₄ d t) = (2 ^ f) ^ 16 := by
  have F := facts h d hlay
  have hMF : yamadaF₄ d t ⊔ d.M.map L.subtype = yamadaM₄ d t := by
    rw [sup_comm, ← yamadaM₄_eq_sup h d hlay]
  have hinf : yamadaF₄ d t ⊓ d.M.map L.subtype = d.F.map L.subtype := by
    refine le_antisymm (fun x hx => ?_) (le_inf (F_le_F₄ d F) (map_mono d.F_le_M))
    rw [← S_map_inf_yamadaF₄ h d hlay]
    exact mem_inf.2 ⟨map_mono d.M_le_S (mem_inf.1 hx).2, (mem_inf.1 hx).1⟩
  have h1 := card_sup_mul_card_inf_eq_D4 (A := yamadaF₄ d t) (B := d.M.map L.subtype)
    ((map_mono d.M_le_S).trans (F.S_le_R₄.trans (R₄_le_N_F₄ d F)))
  rw [hMF, hinf, card_yamadaM₄ h d hlay, card_map_of_injective L.subtype_injective,
    card_map_of_injective L.subtype_injective, d.card_F, d.card_M] at h1
  refine Nat.eq_of_mul_eq_mul_right (m := (2 ^ f) ^ 11) (by positivity) ?_
  calc Nat.card (yamadaF₄ d t) * (2 ^ f) ^ 11 = (2 ^ f) ^ 19 * (2 ^ f) ^ 8 := h1.symm
    _ = (2 ^ f) ^ 16 * (2 ^ f) ^ 11 := by ring

theorem card_yamadaS₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    Nat.card (yamadaS₄ d t) = (2 ^ f) ^ 20 := by
  have F := facts h d hlay
  have h1 := card_sup_mul_card_inf_eq_D4 (A := yamadaF₄ d t) (B := d.S.map L.subtype)
    (F.S_le_R₄.trans (R₄_le_N_F₄ d F))
  rw [← yamadaS₄_eq_yamadaF₄_sup_S h d hlay, inf_comm, S_map_inf_yamadaF₄ h d hlay,
    card_yamadaF₄ h d hlay, card_map_of_injective L.subtype_injective,
    card_map_of_injective L.subtype_injective, d.card_F, d.card_S] at h1
  refine Nat.eq_of_mul_eq_mul_right (m := (2 ^ f) ^ 8) (by positivity) ?_
  calc Nat.card (yamadaS₄ d t) * (2 ^ f) ^ 8 = (2 ^ f) ^ 16 * (2 ^ f) ^ 12 := h1
    _ = (2 ^ f) ^ 20 * (2 ^ f) ^ 8 := by ring

end Orders

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
