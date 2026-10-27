module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalPTwo

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open scoped commutatorElement

section Generic

variable {X : Type*} [Group X]

theorem commutator_mem_of_mul_self_mem_PA {A F : Subgroup X}
    (hA : A ≤ normalizer (F : Set X)) (hsq : ∀ a ∈ A, a * a ∈ F) {a a' : X} (ha : a ∈ A)
    (ha' : a' ∈ A) : a * a' * a⁻¹ * a'⁻¹ ∈ F := by
  have h1 : a⁻¹ * a⁻¹ ∈ F := by
    have := inv_mem (hsq a ha)
    rwa [mul_inv_rev] at this
  have h2 : a'⁻¹ * a'⁻¹ ∈ F := by
    have := inv_mem (hsq a' ha')
    rwa [mul_inv_rev] at this
  have e : a * a' * a⁻¹ * a'⁻¹ = (a * a' * (a * a')) * (a'⁻¹ * (a⁻¹ * a⁻¹) * a'⁻¹⁻¹) *
      (a'⁻¹ * a'⁻¹) := by group
  rw [e]
  exact mul_mem (mul_mem (hsq _ (mul_mem ha ha')) ((mem_normalizer_iff.1 (inv_mem (hA ha')) _).1
    h1)) h2

private def sqSub_PA (H F : Subgroup X) (hH : H ≤ normalizer (F : Set X))
    (hc : ∀ x ∈ H, ∀ y ∈ H, x * y * x⁻¹ * y⁻¹ ∈ F) : Subgroup X where
  carrier := {x | x ∈ H ∧ x * x ∈ F}
  mul_mem' := by
    rintro x y ⟨hx, hxF⟩ ⟨hy, hyF⟩
    show x * y ∈ H ∧ x * y * (x * y) ∈ F
    refine ⟨mul_mem hx hy, ?_⟩
    have e : x * y * (x * y) = (x * y * x⁻¹ * y⁻¹) * (y * (x * x) * y⁻¹) * (y * y) := by group
    rw [e]
    exact mul_mem (mul_mem (hc x hx y hy) ((mem_normalizer_iff.1 (hH hy) _).1 hxF)) hyF
  one_mem' := by
    show (1 : X) ∈ H ∧ (1 : X) * 1 ∈ F
    exact ⟨one_mem H, by rw [mul_one]; exact one_mem F⟩
  inv_mem' := by
    rintro x ⟨hx, hxF⟩
    show x⁻¹ ∈ H ∧ x⁻¹ * x⁻¹ ∈ F
    refine ⟨inv_mem hx, ?_⟩
    have := inv_mem hxF
    rwa [mul_inv_rev] at this

private theorem mem_sqSub_PA {H F : Subgroup X} {hH : H ≤ normalizer (F : Set X)}
    {hc : ∀ x ∈ H, ∀ y ∈ H, x * y * x⁻¹ * y⁻¹ ∈ F} {x : X} :
    x ∈ sqSub_PA H F hH hc ↔ x ∈ H ∧ x * x ∈ F :=
  Iff.rfl

theorem mul_self_commutator_mem_sup_PA {A B F : Subgroup X}
    (hA : A ≤ normalizer (F : Set X)) (hB : B ≤ normalizer (F : Set X))
    (hAsq : ∀ a ∈ A, a * a ∈ F) (hBsq : ∀ b ∈ B, b * b ∈ F)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ * b⁻¹ ∈ F) :
    (∀ x ∈ A ⊔ B, x * x ∈ F) ∧ ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y * x⁻¹ * y⁻¹ ∈ F := by
  have hBA : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ * a⁻¹ ∈ F := fun b hb a ha => by
    have := inv_mem (hAB a ha b hb)
    rwa [show (a * b * a⁻¹ * b⁻¹)⁻¹ = b * a * b⁻¹ * a⁻¹ by group] at this
  have hAs : A ⊔ B ≤ modCentralizerSub A F :=
    sup_le (fun a ha => mem_modCentralizerSub.2 ⟨hA ha, fun a' ha' =>
      commutator_mem_of_mul_self_mem_PA hA hAsq ha ha'⟩)
      (fun b hb => mem_modCentralizerSub.2 ⟨hB hb, fun a ha => hBA b hb a ha⟩)
  have hBs : A ⊔ B ≤ modCentralizerSub B F :=
    sup_le (fun a ha => mem_modCentralizerSub.2 ⟨hA ha, fun b hb => hAB a ha b hb⟩)
      (fun b hb => mem_modCentralizerSub.2 ⟨hB hb, fun b' hb' =>
        commutator_mem_of_mul_self_mem_PA hB hBsq hb hb'⟩)
  have hc : ∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, x * y * x⁻¹ * y⁻¹ ∈ F := by
    have hH : A ⊔ B ≤ modCentralizerSub (A ⊔ B) F := by
      refine sup_le (fun a ha => mem_modCentralizerSub.2 ⟨hA ha, fun y hy => ?_⟩)
        (fun b hb => mem_modCentralizerSub.2 ⟨hB hb, fun y hy => ?_⟩)
      · have := inv_mem ((mem_modCentralizerSub.1 (hAs hy)).2 a ha)
        rwa [show (y * a * y⁻¹ * a⁻¹)⁻¹ = a * y * a⁻¹ * y⁻¹ by group] at this
      · have := inv_mem ((mem_modCentralizerSub.1 (hBs hy)).2 b hb)
        rwa [show (y * b * y⁻¹ * b⁻¹)⁻¹ = b * y * b⁻¹ * y⁻¹ by group] at this
    intro x hx y hy
    exact (mem_modCentralizerSub.1 (hH hx)).2 y hy
  refine ⟨fun x hx => ?_, hc⟩
  have hsub : A ⊔ B ≤ sqSub_PA (A ⊔ B) F (sup_le hA hB) hc :=
    sup_le (fun a ha => mem_sqSub_PA.2 ⟨mem_sup_left ha, hAsq a ha⟩)
      (fun b hb => mem_sqSub_PA.2 ⟨mem_sup_right hb, hBsq b hb⟩)
  exact (mem_sqSub_PA.1 (hsub hx)).2

theorem map_conj_map_conj_PA {v : X} (hv : v * v = 1) (H : Subgroup X) :
    (H.map (MulAut.conj v).toMonoidHom).map (MulAut.conj v).toMonoidHom = H := by
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  ext x
  rw [mem_map_conj_iff_D4, mem_map_conj_iff_D4, hvi,
    show v * (v * x * v) * v = (v * v) * x * (v * v) by group, hv, one_mul, mul_one]

theorem mul_self_commutator_mem_of_le_sup_conj_PA {M F W : Subgroup X} {v : X} (hv : v * v = 1)
    (hFM : F ≤ M) (hvM : v ∈ normalizer (M : Set X)) (hvW : v ∈ normalizer (W : Set X))
    (hMF : M ≤ normalizer (F : Set X)) (hMW : M ≤ normalizer (W : Set X))
    (hsq : ∀ x ∈ F, x * x ∈ W) (hcap : F ⊓ F.map (MulAut.conj v).toMonoidHom ≤ W)
    (hM : M ≤ F ⊔ F.map (MulAut.conj v).toMonoidHom) :
    (∀ x ∈ M, x * x ∈ W) ∧ ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ W := by
  have hBM : F.map (MulAut.conj v).toMonoidHom ≤ M := by
    intro z hz
    rw [mem_map_conj_iff_D4] at hz
    have := (mem_normalizer_iff.1 hvM _).1 (hFM hz)
    rwa [show v * (v⁻¹ * z * v) * v⁻¹ = z by group] at this
  have hBsq : ∀ b ∈ F.map (MulAut.conj v).toMonoidHom, b * b ∈ W := by
    intro b hb
    rw [mem_map_conj_iff_D4] at hb
    have := (mem_normalizer_iff.1 hvW _).1 (hsq _ hb)
    rwa [show v * ((v⁻¹ * b * v) * (v⁻¹ * b * v)) * v⁻¹ = b * b by group] at this
  have hAB : ∀ a ∈ F, ∀ b ∈ F.map (MulAut.conj v).toMonoidHom, a * b * a⁻¹ * b⁻¹ ∈ W := by
    intro a ha b hb
    have hbM := hBM hb
    have haM := hFM ha
    have h1 : a * b * a⁻¹ * b⁻¹ ∈ F := by
      have := mul_mem ha ((mem_normalizer_iff.1 (hMF hbM) _).1 (inv_mem ha))
      rwa [show a * (b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ by group] at this
    have h2 : a * b * a⁻¹ * b⁻¹ ∈ F.map (MulAut.conj v).toMonoidHom := by
      rw [mem_map_conj_iff_D4]
      have ha' : v⁻¹ * a * v ∈ M := (mem_normalizer_iff''.1 hvM a).1 haM
      have hb' : v⁻¹ * b * v ∈ F := mem_map_conj_iff_D4.1 hb
      have := mul_mem ((mem_normalizer_iff.1 (hMF ha') _).1 hb') (inv_mem hb')
      rwa [show v⁻¹ * a * v * (v⁻¹ * b * v) * (v⁻¹ * a * v)⁻¹ * (v⁻¹ * b * v)⁻¹ =
        v⁻¹ * (a * b * a⁻¹ * b⁻¹) * v by group] at this
    exact hcap ⟨h1, h2⟩
  obtain ⟨hsqM, hcM⟩ := mul_self_commutator_mem_sup_PA (fun a ha => hMW (hFM ha))
    (fun b hb => hMW (hBM hb)) hsq hBsq hAB
  exact ⟨fun x hx => hsqM x (hM hx), fun x hx y hy => hcM x (hM hx) y (hM hy)⟩

end Generic

set_option hygiene false in
local macro "layer_ctx_PA" : tactic => `(tactic| (
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
  have h521 := h.yamada_5_21 d hlay))

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

theorem yamadaP_sup_zpowers_le_normalizer_yamadaR₄_PA (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaP d t ⊔ zpowers t ≤ normalizer (yamadaR₄ d t : Set G) := by
  rw [(h.yamada_5_32_of_layerHyp d hlay).1]
  exact le_sup_left

theorem yamadaP_le_normalizer_yamadaR₄_PA (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaP d t ≤ normalizer (yamadaR₄ d t : Set G) :=
  le_sup_left.trans (h.yamadaP_sup_zpowers_le_normalizer_yamadaR₄_PA d hlay)

theorem yamadaP_le_normalizer_yamadaW₃_PA (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaP d t ≤ normalizer (yamadaW₃ d t : Set G) := fun _ hx =>
  (mem_inf.1 (mem_inf.1 (h.normalizer_yamadaR₄_le_of_layerHyp d hlay
    (h.yamadaP_le_normalizer_yamadaR₄_PA d hlay hx))).1).2

theorem yamadaP_le_normalizer_yamadaY₂_PA (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaP d t ≤ normalizer (yamadaY₂ d t : Set G) := fun _ hx =>
  (mem_inf.1 (h.normalizer_yamadaR₄_le_of_layerHyp d hlay
    (h.yamadaP_le_normalizer_yamadaR₄_PA d hlay hx))).2

theorem yamadaP_le_normalizer_yamadaF₄_PA (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaP d t ≤ normalizer (yamadaF₄ d t : Set G) := fun _ hx =>
  (mem_inf.1 (h.normalizer_yamadaR₄_le_normalizer_yamadaF₄ d hlay
    (h.yamadaP_le_normalizer_yamadaR₄_PA d hlay hx))).2

theorem yamadaF₄_le_yamadaD₅_PA (d : TrialityD4Data L (2 ^ f)) :
    yamadaF₄ d t ≤ yamadaD₅ d t :=
  (yamadaF₄_le_yamadaD₄ d t).trans inf_le_right

theorem yamadaW₃_le_yamadaD₅_PA (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaW₃ d t ≤ yamadaD₅ d t :=
  (h.yamadaW₃_le_yamadaF₄_R5 d hlay).trans (yamadaF₄_le_yamadaD₅_PA d)

theorem yamadaF₄_le_yamadaM₆_PA (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaF₄ d t ≤ yamadaM₆ d t :=
  (yamadaF₄_le_yamadaM₄ d t).trans (h.yamadaM₄_le_yamadaM₆ d hlay)

theorem commutator_mem_yamadaV₁_of_mem_yamadaD₅_PA (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {x y : G} (hx : x ∈ yamadaD₅ d t)
    (hy : y ∈ yamadaD₅ d t) : x * y * x⁻¹ * y⁻¹ ∈ yamadaV₁ d t := by
  layer_ctx_PA
  have h1 : ⁅x, y⁆ ∈ ⁅yamadaD₅ d t, yamadaD₅ d t⁆ := commutator_mem_commutator hx hy
  rw [(h.yamada_5_25 d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e h520 h5221 h521).1,
    commutatorElement_def] at h1
  exact h1

theorem mul_self_mem_yamadaV₁_of_mem_yamadaD₅_PA (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {x : G} (hx : x ∈ yamadaD₅ d t) :
    x * x ∈ yamadaV₁ d t := by
  layer_ctx_PA
  exact h.mul_self_mem_yamadaV₁_of_mem_yamadaD₅ d hNH h561 h562 h591 h592 h593 h5101 h5102 h59e
    h520 h5221 h521 hx

theorem mul_self_mem_yamadaR₄_of_mem_sup_PA (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} (hx : x ∈ yamadaP d t ⊔ zpowers t) : x * x ∈ yamadaR₄ d t := by
  have hS₄c : ∀ x ∈ yamadaS₄ d t, ∀ y ∈ yamadaS₄ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaF₄ d t :=
    fun _ hx _ hy => h.commutator_mem_yamadaF₄_of_mem_yamadaS₄ d hlay hx hy
  have htS₄ : ∀ x ∈ yamadaS₄ d t, t * x * t * x⁻¹ ∈ yamadaF₄ d t :=
    fun _ hx => h.crossed_mem_yamadaF₄_of_mem_yamadaS₄ d hlay hx
  have hKF : normalizer (yamadaR₄ d t : Set G) ≤ normalizer (yamadaF₄ d t : Set G) :=
    (h.normalizer_yamadaR₄_le_normalizer_yamadaF₄ d hlay).trans inf_le_right
  have hP := h.yamada_5_32_of_layerHyp d hlay
  exact h.mul_self_mem_yamadaR₄_P d hlay
    (fun _ hx => h.mul_self_mem_yamadaF₄_of_mem_yamadaS₄ d hlay hx) (h.S_map_inf_yamadaF₄ d hlay)
    hKF (h.commutator_mem_yamadaF₄_of_mem_yamadaR₅ d hlay hS₄c htS₄)
    (h.centralizer_inf_normalizer_S_le_normalizer_yamadaR₄ d hlay)
    (show x ∈ h.yamadaE₄ d hlay hKF from
      ⟨h.yamadaP_sup_zpowers_le_normalizer_yamadaR₄_PA d hlay hx, hP.2.2.2.2.2.2.2 x hx⟩)

theorem commutator_mem_yamadaR₄_of_mem_sup_PA (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x y : G} (hx : x ∈ yamadaP d t ⊔ zpowers t)
    (hy : y ∈ yamadaP d t ⊔ zpowers t) : x * y * x⁻¹ * y⁻¹ ∈ yamadaR₄ d t :=
  commutator_mem_of_mul_self_mem_PA (h.yamadaP_sup_zpowers_le_normalizer_yamadaR₄_PA d hlay)
    (fun _ ha => h.mul_self_mem_yamadaR₄_of_mem_sup_PA d hlay ha) hx hy

theorem mem_yamadaD₄_of_commutator_mem_yamadaV₁_PA (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {z : G} (hz : z ∈ yamadaS₄ d t)
    (hc : ∀ w ∈ yamadaW₃ d t, z * w * z⁻¹ * w⁻¹ ∈ yamadaV₁ d t) : z ∈ yamadaD₄ d t := by
  have h562 := h.yamada_5_6_2 d hlay
  have hSN : d.S.map L.subtype ≤ normalizer (yamadaF₄ d t : Set G) := fun s hs =>
    h.yamadaR₄_le_normalizer_yamadaF₄_S4 d hlay (h.S_map_le_yamadaR₄_R4 d hlay hs)
  have hz' : z ∈ ((yamadaF₄ d t ⊔ d.S.map L.subtype : Subgroup G) : Set G) := by
    rw [← h.yamadaS₄_eq_yamadaF₄_sup_S d hlay]
    exact hz
  rw [coe_mul_of_right_le_normalizer_left _ _ hSN, Set.mem_mul] at hz'
  obtain ⟨φ, hφ, _, ⟨s, hs, rfl⟩, rfl⟩ := hz'
  have hsD : s ∈ d.D := by
    refine d.mem_D_of_commutatorElement_mem_V hs fun w hw => ?_
    have hwW₃ : ((w : L) : G) ∈ yamadaW₃ d t := h.W_map_le_yamadaW₃_S4C d hlay ⟨w, hw, rfl⟩
    have hφw : φ * (w : G) * φ⁻¹ * (w : G)⁻¹ ∈ yamadaV₁ d t :=
      h.commutator_mem_yamadaV₁_of_mem_yamadaD₅_PA d hlay (yamadaF₄_le_yamadaD₅_PA d hφ)
        (h.yamadaW₃_le_yamadaD₅_PA d hlay hwW₃)
    have hφN : φ ∈ normalizer (yamadaV₁ d t : Set G) :=
      Subgroup.centralizer_le_normalizer _ (mem_inf.1 (yamadaF₄_le_yamadaD₅_PA d hφ)).2
    have h2 := mul_mem (hc _ hwW₃) (inv_mem hφw)
    have hV : (s : G) * (w : G) * (s : G)⁻¹ * (w : G)⁻¹ ∈ yamadaV₁ d t := by
      have h3 : φ * ((s : G) * (w : G) * (s : G)⁻¹ * (w : G)⁻¹) * φ⁻¹ ∈ yamadaV₁ d t := by
        have e : φ * ((s : G) * (w : G) * (s : G)⁻¹ * (w : G)⁻¹) * φ⁻¹ =
            (φ * (L.subtype s) * (w : G) * (φ * (L.subtype s))⁻¹ * (w : G)⁻¹) *
              (φ * (w : G) * φ⁻¹ * (w : G)⁻¹)⁻¹ := by
          simp only [Subgroup.coe_subtype]
          group
        rw [e]
        exact h2
      have := (mem_normalizer_iff.1 (inv_mem hφN) _).1 h3
      rwa [show φ⁻¹ * (φ * ((s : G) * (w : G) * (s : G)⁻¹ * (w : G)⁻¹) * φ⁻¹) * φ⁻¹⁻¹ =
        (s : G) * (w : G) * (s : G)⁻¹ * (w : G)⁻¹ by group] at this
    have hD : (s : G) * (w : G) * (s : G)⁻¹ * (w : G)⁻¹ ∈ d.D.map L.subtype :=
      ⟨s * w * s⁻¹ * w⁻¹, (d.W_le_F.trans d.F_le_D)
        (mul_mem ((mem_normalizer_iff.1 (d.S_le_normalizer_W hs) w).1 hw) (inv_mem hw)), rfl⟩
    have hmem : ((s * w * s⁻¹ * w⁻¹ : L) : G) ∈ yamadaV₁ d t ⊓ d.D.map L.subtype :=
      mem_inf.2 ⟨hV, hD⟩
    rw [h.yamadaV₁_inf_D d h562] at hmem
    obtain ⟨z', hz', hze⟩ := hmem
    rwa [← Subtype.ext hze]
  rw [h.yamadaD₄_eq_sup d hlay]
  exact mul_mem (mem_sup_right hφ) (mem_sup_left ⟨s, hsD, rfl⟩)

theorem commutator_mem_yamadaF₄_of_mem_yamadaD₅_of_mem_yamadaM₆_PA (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {x m : G} (hx : x ∈ yamadaD₅ d t)
    (hm : m ∈ yamadaM₆ d t) : x * m * x⁻¹ * m⁻¹ ∈ yamadaF₄ d t := by
  have hxP := yamadaD₅_le_yamadaP d t hx
  have hmP := yamadaM₆_le_yamadaP d t hm
  have hcP : x * m * x⁻¹ * m⁻¹ ∈ yamadaP d t :=
    mul_mem (mul_mem (mul_mem hxP hmP) (inv_mem hxP)) (inv_mem hmP)
  have hcR₄ : x * m * x⁻¹ * m⁻¹ ∈ yamadaR₄ d t :=
    h.commutator_mem_yamadaR₄_of_mem_sup_PA d hlay (mem_sup_left hxP) (mem_sup_left hmP)
  have hmY₂ : m ∈ centralizer (yamadaY₂ d t : Set G) :=
    (inf_le_right : yamadaM₆ d t ≤ centralizer (yamadaY₂ d t : Set G)) hm
  have hcY₂ : x * m * x⁻¹ * m⁻¹ ∈ centralizer (yamadaY₂ d t : Set G) :=
    mul_mem ((mem_normalizer_iff.1 (mem_normalizer_centralizer_C8
      (h.yamadaP_le_normalizer_yamadaY₂_PA d hlay hxP)) m).1 hmY₂) (inv_mem hmY₂)
  have hV₁N : ∀ g ∈ yamadaP d t, g ∈ normalizer (yamadaV₁ d t : Set G) := fun g hg =>
    Subgroup.centralizer_le_normalizer _ (yamadaP_le_centralizer_yamadaV₁ d t hg)
  let Z := Common.centralizerMod (normalizer (yamadaW₃ d t : Set G) ⊓
      normalizer (yamadaV₁ d t : Set G)) (yamadaW₃ d t) (yamadaV₁ d t)
    (fun g hg y hy => (mem_normalizer_iff.1 (mem_inf.1 hg).1 y).1 hy)
    (fun g hg b hb => (mem_normalizer_iff.1 (mem_inf.1 hg).2 b).1 hb)
  have hxZ : x ∈ Z := Common.mem_centralizerMod.2
    ⟨⟨h.yamadaP_le_normalizer_yamadaW₃_PA d hlay hxP, hV₁N x hxP⟩, fun y hy =>
      h.commutator_mem_yamadaV₁_of_mem_yamadaD₅_PA d hlay hx (h.yamadaW₃_le_yamadaD₅_PA d hlay hy)⟩
  have hmN : m ∈ normalizer (yamadaW₃ d t : Set G) ⊓ normalizer (yamadaV₁ d t : Set G) :=
    ⟨h.yamadaP_le_normalizer_yamadaW₃_PA d hlay hmP, hV₁N m hmP⟩
  have hcZ : x * m * x⁻¹ * m⁻¹ ∈ Z := by
    have := mul_mem hxZ (Common.conj_mem_centralizerMod hmN (inv_mem hxZ))
    rwa [show x * (m * x⁻¹ * m⁻¹) = x * m * x⁻¹ * m⁻¹ by group] at this
  have hcD₄ : x * m * x⁻¹ * m⁻¹ ∈ yamadaD₄ d t :=
    h.mem_yamadaD₄_of_commutator_mem_yamadaV₁_PA d hlay
      (mem_inf.2 ⟨hcR₄, yamadaP_le_centralizer_yamadaV₁ d t hcP⟩)
      (Common.mem_centralizerMod.1 hcZ).2
  exact mem_inf.2 ⟨mem_inf.2 ⟨hcR₄, hcY₂⟩, hcD₄⟩

theorem v_mem_normalizer_yamadaM₆_PA (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : ((d.v : L) : G) ∈ normalizer (yamadaM₆ d t : Set G) :=
  mem_normalizer_inf_D4 (le_normalizer_yamadaL₆ d t
    ⟨h.v_mem_normalizer_yamadaL₃ d, h.v_mem_normalizer_yamadaM₃ d hlay⟩)
    (mem_normalizer_centralizer_C8 (v_mem_normalizer_yamadaY₂ d))

theorem yamadaM₄_le_yamadaL₄_PA (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaM₄ d t ≤ yamadaL₄ d t := fun _ hm =>
  mem_inf.2 ⟨(mem_inf.1 hm).1, centralizer_le (h.Y_map_le_yamadaY₂ d hlay) (mem_inf.1 hm).2⟩

theorem yamadaF₄_inf_yamadaL₃_le_yamadaF₃_PA (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaF₄ d t ⊓ yamadaL₃ d t ≤ yamadaF₃ d t := by
  rintro z ⟨hzF, hzL⟩
  have hzY₂ : z ∈ centralizer (yamadaY₂ d t : Set G) := (mem_inf.1 (mem_inf.1 hzF).1).2
  have hzD₅ : z ∈ yamadaD₅ d t := (mem_inf.1 (mem_inf.1 hzF).2).2
  exact mem_inf.2 ⟨mem_inf.2 ⟨hzL, hzY₂⟩, mem_inf.2 ⟨mem_inf.2
    ⟨h.yamadaL₃_le_yamadaR₃_D3 d hlay hzL, (mem_inf.1 hzD₅).2⟩, (mem_inf.1 hzD₅).1⟩⟩

theorem yamadaF₄_inf_map_conj_le_yamadaW₃_PA (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaF₄ d t ⊓ (yamadaF₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom ≤
      yamadaW₃ d t := by
  intro z hz
  obtain ⟨hz₁, hz₂⟩ := mem_inf.1 hz
  have hL₄ : z ∈ yamadaL₄ d t ⊓
      (yamadaL₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom := by
    refine mem_inf.2 ⟨h.yamadaM₄_le_yamadaL₄_PA d hlay (yamadaF₄_le_yamadaM₄ d t hz₁), ?_⟩
    rw [mem_map_conj_iff_D4] at hz₂ ⊢
    exact h.yamadaM₄_le_yamadaL₄_PA d hlay (yamadaF₄_le_yamadaM₄ d t hz₂)
  rw [h.yamadaL₄_inf_map_conj_yamadaL₄ d hlay] at hL₄
  have h1 : z ∈ yamadaF₃ d t := h.yamadaF₄_inf_yamadaL₃_le_yamadaF₃_PA d hlay ⟨hz₁, hL₄⟩
  have h2 : z ∈ (yamadaF₃ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom := by
    rw [mem_map_conj_iff_D4] at hz₂ ⊢
    exact h.yamadaF₄_inf_yamadaL₃_le_yamadaF₃_PA d hlay ⟨hz₂,
      (mem_normalizer_iff''.1 (h.v_mem_normalizer_yamadaL₃ d) z).1 hL₄⟩
  rw [(h.yamada_5_21 d hlay).1]
  exact ⟨h1, h2⟩

theorem yamadaM₆_le_sup_map_conj_yamadaF₄_PA (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaM₆ d t ≤ yamadaF₄ d t ⊔
      (yamadaF₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom := by
  have hv : ((d.v : L) : G) * ((d.v : L) : G) = 1 := coe_v_mul_self d
  have hM₄ : yamadaM₄ d t ≤ yamadaF₄ d t ⊔
      (yamadaF₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom := by
    rw [h.yamadaM₄_eq_sup d hlay]
    refine sup_le ((h.yamadaM_map_le_yamadaM₃_R5 d hlay).trans ?_) le_sup_left
    rw [h.yamadaM₃_eq_sup d hlay]
    exact sup_le_sup (h.yamadaF₃_le_yamadaF₄_R5 d hlay)
      (Subgroup.map_mono (h.yamadaF₃_le_yamadaF₄_R5 d hlay))
  have hΦ : (yamadaF₄ d t ⊔
      (yamadaF₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom).map
        (MulAut.conj ((d.v : L) : G)).toMonoidHom ≤ yamadaF₄ d t ⊔
      (yamadaF₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom := by
    rw [Subgroup.map_sup, map_conj_map_conj_PA hv]
    exact sup_le le_sup_right le_sup_left
  rw [(h.yamada_5_29_1_of_layerHyp d hlay).2.2]
  exact sup_le hM₄ ((Subgroup.map_mono hM₄).trans hΦ)

theorem mul_self_commutator_mem_yamadaW₃_of_mem_yamadaM₆_PA (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    (∀ x ∈ yamadaM₆ d t, x * x ∈ yamadaW₃ d t) ∧
      ∀ x ∈ yamadaM₆ d t, ∀ y ∈ yamadaM₆ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaW₃ d t :=
  mul_self_commutator_mem_of_le_sup_conj_PA (coe_v_mul_self d) (h.yamadaF₄_le_yamadaM₆_PA d hlay)
    (h.v_mem_normalizer_yamadaM₆_PA d hlay) (h.v_mem_normalizer_yamadaW₃ d)
    (fun _ hx => h.yamadaP_le_normalizer_yamadaF₄_PA d hlay (yamadaM₆_le_yamadaP d t hx))
    (fun _ hx => h.yamadaP_le_normalizer_yamadaW₃_PA d hlay (yamadaM₆_le_yamadaP d t hx))
    (fun _ hx => h.mul_self_mem_yamadaW₃_of_mem_yamadaF₄_S4 d hlay hx)
    (h.yamadaF₄_inf_map_conj_le_yamadaW₃_PA d hlay)
    (h.yamadaM₆_le_sup_map_conj_yamadaF₄_PA d hlay)

theorem mul_self_mem_yamadaW₃_of_mem_yamadaM₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} (hx : x ∈ yamadaM₆ d t) : x * x ∈ yamadaW₃ d t :=
  (h.mul_self_commutator_mem_yamadaW₃_of_mem_yamadaM₆_PA d hlay).1 x hx

theorem commutator_mem_yamadaW₃_of_mem_yamadaM₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x y : G} (hx : x ∈ yamadaM₆ d t) (hy : y ∈ yamadaM₆ d t) :
    x * y * x⁻¹ * y⁻¹ ∈ yamadaW₃ d t :=
  (h.mul_self_commutator_mem_yamadaW₃_of_mem_yamadaM₆_PA d hlay).2 x hx y hy

theorem mul_self_commutator_mem_yamadaF₄_of_mem_yamadaP_PA (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    (∀ x ∈ yamadaP d t, x * x ∈ yamadaF₄ d t) ∧
      ∀ x ∈ yamadaP d t, ∀ y ∈ yamadaP d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaF₄ d t :=
  mul_self_commutator_mem_sup_PA
    (fun _ hx => h.yamadaP_le_normalizer_yamadaF₄_PA d hlay (yamadaD₅_le_yamadaP d t hx))
    (fun _ hx => h.yamadaP_le_normalizer_yamadaF₄_PA d hlay (yamadaM₆_le_yamadaP d t hx))
    (fun _ hx => h.yamadaV₁_le_yamadaF₄_R5 d hlay
      (h.mul_self_mem_yamadaV₁_of_mem_yamadaD₅_PA d hlay hx))
    (fun _ hx => h.yamadaW₃_le_yamadaF₄_R5 d hlay
      (h.mul_self_mem_yamadaW₃_of_mem_yamadaM₆ d hlay hx))
    (fun _ hx _ hm => h.commutator_mem_yamadaF₄_of_mem_yamadaD₅_of_mem_yamadaM₆_PA d hlay hx hm)

theorem mul_self_mem_yamadaF₄_of_mem_yamadaP (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} (hx : x ∈ yamadaP d t) : x * x ∈ yamadaF₄ d t :=
  (h.mul_self_commutator_mem_yamadaF₄_of_mem_yamadaP_PA d hlay).1 x hx

theorem commutator_mem_yamadaF₄_of_mem_yamadaP (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x y : G} (hx : x ∈ yamadaP d t) (hy : y ∈ yamadaP d t) :
    x * y * x⁻¹ * y⁻¹ ∈ yamadaF₄ d t :=
  (h.mul_self_commutator_mem_yamadaF₄_of_mem_yamadaP_PA d hlay).2 x hx y hy

theorem yamadaD₅_le_normalizer_yamadaM₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaD₅ d t ≤ normalizer (yamadaM₆ d t : Set G) := by
  intro x hx
  refine mem_normalizer_fintype fun m hm => ?_
  have h1 := mul_mem (h.yamadaF₄_le_yamadaM₆_PA d hlay
    (h.commutator_mem_yamadaF₄_of_mem_yamadaD₅_of_mem_yamadaM₆_PA d hlay hx hm)) hm
  rwa [show x * m * x⁻¹ * m⁻¹ * m = x * m * x⁻¹ by group] at h1

theorem yamadaM₆_le_normalizer_yamadaD₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaM₆ d t ≤ normalizer (yamadaD₅ d t : Set G) := by
  intro m hm
  refine mem_normalizer_fintype fun x hx => ?_
  have h1 := mul_mem (yamadaF₄_le_yamadaD₅_PA d
    (inv_mem (h.commutator_mem_yamadaF₄_of_mem_yamadaD₅_of_mem_yamadaM₆_PA d hlay hx hm))) hx
  rwa [show (x * m * x⁻¹ * m⁻¹)⁻¹ * x = m * x * m⁻¹ by group] at h1

theorem yamadaP_le_normalizer_yamadaM₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaP d t ≤ normalizer (yamadaM₆ d t : Set G) :=
  sup_le (h.yamadaD₅_le_normalizer_yamadaM₆ d hlay) le_normalizer

theorem yamadaP_le_normalizer_yamadaD₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaP d t ≤ normalizer (yamadaD₅ d t : Set G) :=
  sup_le le_normalizer (h.yamadaM₆_le_normalizer_yamadaD₅ d hlay)

theorem yamadaD₅_inf_yamadaM₆_le_yamadaF₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaD₅ d t ⊓ yamadaM₆ d t ≤ yamadaF₄ d t := by
  intro z hz
  obtain ⟨hzD, hzM⟩ := mem_inf.1 hz
  layer_ctx_PA
  have hzP : z ∈ yamadaP d t := yamadaD₅_le_yamadaP d t hzD
  have hzL₆ : z ∈ yamadaL₆ d t := (inf_le_left : yamadaM₆ d t ≤ yamadaL₆ d t) hzM
  obtain ⟨m, hm, hzm⟩ := h.conj_t_mem_of_mem_yamadaL₆ d hlay hzL₆
  obtain ⟨δ, hδ, hzδ⟩ :=
    (h.yamada_5_12 d hNH h561 h562 h591 h592 h593).2.1.1 z (mem_inf.1 hzD).1
  have hmδ : m = δ := mul_left_cancel (hzm.symm.trans hzδ)
  subst hmδ
  have hmF₃ : m ∈ yamadaF₃ d t :=
    mem_inf.2 ⟨hm, h.yamadaD₁_le_yamadaD₃_C9 d hNH h561 h562 h591 h592 h593 hδ⟩
  have hzN : z ∈ normalizer ((yamadaF₄ d t ⊔ zpowers t : Subgroup G) : Set G) :=
    h.mem_normalizer_sup_zpowers_D3 (h.t_mem_normalizer_yamadaF₄ d hlay)
      (h.yamadaP_le_normalizer_yamadaF₄_PA d hlay hzP) (by
        rw [hzm]
        exact mul_mem (mem_sup_right (mem_zpowers t))
          (mem_sup_left (h.yamadaF₃_le_yamadaF₄_R5 d hlay hmF₃)))
  have hzR₄ : z ∈ yamadaR₄ d t := by
    rw [← (h.yamada_5_32_of_layerHyp d hlay).2.2.2.2.2.2.1]
    exact mem_inf.2 ⟨mem_sup_left hzP, hzN⟩
  exact mem_inf.2 ⟨mem_inf.2 ⟨hzR₄, (mem_inf.1 hzM).2⟩, mem_inf.2 ⟨hzR₄, hzD⟩⟩

theorem yamadaD₅_inf_yamadaM₆_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaD₅ d t ⊓ yamadaM₆ d t = yamadaF₄ d t :=
  le_antisymm (h.yamadaD₅_inf_yamadaM₆_le_yamadaF₄ d hlay)
    (le_inf (yamadaF₄_le_yamadaD₅_PA d) (h.yamadaF₄_le_yamadaM₆_PA d hlay))

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
