module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Seven
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL3Defs
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL3Prelim

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open scoped commutatorElement Pointwise

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem W_inf_conj_u : d.W ⊓ d.W.map (MulAut.conj d.u).toMonoidHom = d.V := by
  have huu := d.u_mul_self
  have hu4 : ∀ a, d.u * d.x₄ a * d.u = d.x₃ a := fun a => by
    rw [← d.u_x₃]
    calc d.u * (d.u * d.x₃ a * d.u) * d.u = (d.u * d.u) * d.x₃ a * (d.u * d.u) := by group
      _ = d.x₃ a := by rw [huu, one_mul, mul_one]
  have hu5 : ∀ a, d.u * d.x₅ a * d.u = d.x₂ a := fun a => by
    rw [← d.u_x₂]
    calc d.u * (d.u * d.x₂ a * d.u) * d.u = (d.u * d.u) * d.x₂ a * (d.u * d.u) := by group
      _ = d.x₂ a := by rw [huu, one_mul, mul_one]
  have hconj : ∀ b₄ b₅ b₆, (MulAut.conj d.u).toMonoidHom (d.nf (0, 0, 0, b₄, b₅, b₆)) =
      d.nf (0, b₅, b₄, 0, 0, b₆) := fun b₄ b₅ b₆ => by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, nf_apply, x₁_zero, x₂_zero,
      x₃_zero, x₄_zero, x₅_zero, one_mul, mul_one, d.u_inv]
    calc d.u * (d.x₄ b₄ * d.x₅ b₅ * d.x₆ b₆) * d.u =
        (d.u * d.x₄ b₄ * d.u) * (d.u * d.x₅ b₅ * d.u) * (d.u * d.x₆ b₆ * d.u) := by
          rw [show (d.u * d.x₄ b₄ * d.u) * (d.u * d.x₅ b₅ * d.u) * (d.u * d.x₆ b₆ * d.u) =
            d.u * d.x₄ b₄ * (d.u * d.u) * d.x₅ b₅ * (d.u * d.u) * d.x₆ b₆ * d.u by group, huu]
          group
      _ = d.x₂ b₅ * d.x₃ b₄ * d.x₆ b₆ := by
          rw [hu4, hu5, d.u_x₆, (d.commute₂₃ b₅ b₄).eq]
  refine le_antisymm ?_ (le_inf (d.V_le_Y.trans d.Y_le_W) ?_)
  · rintro g ⟨hg, w, hw, rfl⟩
    obtain ⟨a₄, a₅, a₆, e⟩ := d.mem_W_coords hg
    obtain ⟨b₄, b₅, b₆, rfl⟩ := d.mem_W_coords hw
    rw [hconj] at e ⊢
    have := d.nf_injective e
    simp only [Prod.mk.injEq] at this
    obtain ⟨-, hb₅, hb₄, -, -, -⟩ := this
    rw [← hb₅, ← hb₄]
    exact ⟨b₆, by simp only [nf_apply, x₁_zero, x₂_zero, x₃_zero, x₄_zero, x₅_zero, one_mul]⟩
  · rintro _ ⟨a, rfl⟩
    refine ⟨d.x₆ a, d.x₆_mem_W a, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, d.u_inv, d.u_x₆]

theorem exists_mul_conj_u_of_mem_D {δ : X} (hδ : δ ∈ d.D) :
    ∃ w₁ ∈ d.W, ∃ w₂ ∈ d.W, δ = w₁ * (d.u * w₂ * d.u⁻¹) := by
  have hWuD : d.W.map (MulAut.conj d.u).toMonoidHom ≤ d.D := by
    rintro _ ⟨w, hw, rfl⟩
    exact (mem_normalizer_iff.1 d.u_mem_normalizer_D w).1 ((d.W_le_F.trans d.F_le_D) hw)
  have hN : d.W.map (MulAut.conj d.u).toMonoidHom ≤ normalizer (d.W : Set X) :=
    hWuD.trans (d.D_le_S.trans d.S_le_normalizer_W)
  have hδ' : δ ∈ ((d.W ⊔ d.W.map (MulAut.conj d.u).toMonoidHom : Subgroup X) : Set X) :=
    d.D_le_W_sup_conj_u hδ
  rw [coe_mul_of_right_le_normalizer_left _ _ hN] at hδ'
  obtain ⟨w₁, hw₁, _, ⟨w₂, hw₂, rfl⟩, e⟩ := hδ'
  exact ⟨w₁, hw₁, w₂, hw₂, e.symm⟩

end TrialityD4Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

section LThree

theorem yamadaY₂_le_centralizer_J₀_D3 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaY₂ d t ≤ centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) := by
  have hV := h.yamadaV₁_le_centralizer_J₀ d hlay
  have hvN : ((d.v : L) : G) ∈ normalizer
      ((centralizer ((d.J₀.map L.subtype : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_centralizer_D4 (coe_mem_normalizer_map d.v_mem_normalizer_J₀)
  refine sup_le hV ?_
  rintro _ ⟨a, ha, rfl⟩
  exact (mem_normalizer_iff.1 hvN a).1 (hV ha)

theorem exists_mem_yamadaM₃_inv_mul_mem (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G}
    (hx : x ∈ yamadaL₃ d t) : ∃ g ∈ yamadaM₃ d t, g⁻¹ * x ∈ yamadaL₂ d t := by
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
  have hY₂N : yamadaL₃ d t ≤ normalizer (yamadaY₂ d t : Set G) := fun g hg =>
    h.normalizer_yamadaV₂_le_normalizer_yamadaY₂ d hNH h561 h562 h591 h592 h593 h5101 h5102
      (h.yamadaL₃_le_normalizer_yamadaV₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hg)
  obtain ⟨m, hm1, hm⟩ := d.exists_mem_ker_nmUnits_ne_one
  have hjJ : ((d.torus (1, m) : L) : G) ∈ d.J₀.map L.subtype := ⟨_, d.torus_one_mem_J₀ hm1, rfl⟩
  have hjY₂ : ∀ a ∈ yamadaY₂ d t, ((d.torus (1, m) : L) : G) * a = a * (d.torus (1, m) : G) :=
    fun a ha => mem_centralizer_iff.1 (h.yamadaY₂_le_centralizer_J₀_D3 d hlay ha) _ hjJ
  have hjYc := J₀_map_le_centralizer_Y d hjJ
  have hjN : ((d.torus (1, m) : L) : G) ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) :=
    Subgroup.mem_inf.2 ⟨h.L_le_centralizer (d.torus (1, m)).2,
      Subgroup.centralizer_le_normalizer _ hjYc⟩
  have hjconj : ∀ c : d.Γ, ((d.torus (1, m) : L) : G) * ((d.x₄ c : L) : G) *
      ((d.torus (1, m) : L) : G)⁻¹ = ((d.x₄ ((m : d.Γ)⁻¹ * c) : L) : G) := fun c => by
    rw [← d.torus_one_conj_x₄ hm1 c]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hν : (1 : d.Γ) + (m : d.Γ)⁻¹ ≠ 0 := by
    intro h0
    have h1 : (m : d.Γ)⁻¹ = 1 :=
      add_left_cancel (h0.trans (CharTwo.add_self_eq_zero (1 : d.Γ)).symm)
    exact hm (Units.ext (by rw [Units.val_one]; exact inv_eq_one.1 h1))
  obtain ⟨hw, ex⟩ := hφ ⟨x, hx⟩
  obtain ⟨w, hwW, hwe⟩ := id hw
  obtain ⟨a, n, hn, rfl⟩ := d.mem_W_iff.1 hwW
  obtain ⟨c, hc⟩ : ∃ c : d.Γ, d.x₄ c * (d.x₄ ((m : d.Γ)⁻¹ * c))⁻¹ = d.x₄ a := by
    refine ⟨((1 : d.Γ) + (m : d.Γ)⁻¹)⁻¹ * a, ?_⟩
    rw [d.x₄_inv, ← d.x₄_add]
    congr 1
    rw [show ∀ z : d.Γ, z + (m : d.Γ)⁻¹ * z = (1 + (m : d.Γ)⁻¹) * z from fun z => by ring,
      ← mul_assoc, mul_inv_cancel₀ hν, one_mul]
  have hA : ((d.x₄ a : L) : G) = ((d.x₄ c : L) : G) * (((d.torus (1, m) : L) : G) *
      ((d.x₄ c : L) : G) * ((d.torus (1, m) : L) : G)⁻¹)⁻¹ := by
    rw [hjconj, ← hc, Subgroup.coe_mul, Subgroup.coe_inv]
  have hx₄c : ((d.x₄ c : L) : G) ∈ d.W.map L.subtype := ⟨_, d.x₄_mem_W c, rfl⟩
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (φ.symm (QuotientGroup.mk ⟨_, hx₄c⟩))
  have hφy : φ (QuotientGroup.mk y) = QuotientGroup.mk ⟨_, hx₄c⟩ := by
    rw [hy, MulEquiv.apply_symm_apply]
  obtain ⟨hwy, ey⟩ := hφ y
  obtain ⟨hjy, hwjy, ejy⟩ := hφeq _ hjN y
  have hz : (t * (y : G) * t * (y : G)⁻¹)⁻¹ * ((d.x₄ c : L) : G) ∈ d.Y.map L.subtype := by
    have := QuotientGroup.eq.1 (ey.symm.trans hφy)
    rwa [mem_subgroupOf] at this
  have hKX : t * (y : G) * t * (y : G)⁻¹ * ((d.x₄ c : L) : G)⁻¹ ∈ d.Y.map L.subtype := by
    obtain ⟨k, hk, hke⟩ := hwy
    have hcomm : t * (y : G) * t * (y : G)⁻¹ * ((d.x₄ c : L) : G)⁻¹ =
        ((d.x₄ c : L) : G)⁻¹ * (t * (y : G) * t * (y : G)⁻¹) := by
      have := congrArg Subtype.val (d.mul_comm_of_mem_W hk (inv_mem (d.x₄_mem_W c)))
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [← hke]
      exact this
    rw [hcomm]
    have := inv_mem hz
    rwa [mul_inv_rev, inv_inv] at this
  have hjK : ((d.torus (1, m) : L) : G) * (t * (y : G) * t * (y : G)⁻¹ *
      ((d.x₄ c : L) : G)⁻¹) * ((d.torus (1, m) : L) : G)⁻¹ =
        t * (y : G) * t * (y : G)⁻¹ * ((d.x₄ c : L) : G)⁻¹ := by
    rw [← mem_centralizer_iff.1 hjYc _ hKX, mul_inv_cancel_right]
  refine ⟨(y : G) * (((d.torus (1, m) : L) : G) * (y : G) * ((d.torus (1, m) : L) : G)⁻¹)⁻¹,
    Subgroup.mem_inf.2 ⟨mul_mem y.2 (inv_mem hjy), ?_⟩, ?_⟩
  ·
    rw [mem_centralizer_iff]
    intro b hb
    have e : (y : G) * (((d.torus (1, m) : L) : G) * (y : G) * ((d.torus (1, m) : L) : G)⁻¹)⁻¹ =
        (y : G) * ((d.torus (1, m) : L) : G) * (y : G)⁻¹ * ((d.torus (1, m) : L) : G)⁻¹ := by
      group
    rw [e]
    have hb' : (y : G)⁻¹ * b * (y : G) ∈ yamadaY₂ d t := by
      have := (mem_normalizer_iff.1 (inv_mem (hY₂N y.2)) b).1 hb
      rwa [inv_inv] at this
    exact (commutator_commute_of_conj_D4 (hjY₂ b hb) (hjY₂ _ hb')).symm
  ·
    have key : φ (QuotientGroup.mk (y * ⟨_, hjy⟩⁻¹)) = φ (QuotientGroup.mk ⟨x, hx⟩) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv, hφy, ejy, ex,
        ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
      show (((d.x₄ c : L) : G) * (((d.torus (1, m) : L) : G) * (t * (y : G) * t * (y : G)⁻¹) *
        ((d.torus (1, m) : L) : G)⁻¹)⁻¹)⁻¹ * (t * x * t * x⁻¹) ∈ d.Y.map L.subtype
      rw [← hwe]
      simp only [map_mul, Subgroup.coe_subtype]
      rw [hA]
      have e : (((d.x₄ c : L) : G) * (((d.torus (1, m) : L) : G) *
          (t * (y : G) * t * (y : G)⁻¹) * ((d.torus (1, m) : L) : G)⁻¹)⁻¹)⁻¹ *
          (((d.x₄ c : L) : G) * (((d.torus (1, m) : L) : G) * ((d.x₄ c : L) : G) *
            ((d.torus (1, m) : L) : G)⁻¹)⁻¹ * (n : G)) =
          ((d.torus (1, m) : L) : G) * (t * (y : G) * t * (y : G)⁻¹ *
            ((d.x₄ c : L) : G)⁻¹) * ((d.torus (1, m) : L) : G)⁻¹ * (n : G) := by
        group
      rw [e, hjK]
      exact mul_mem hKX ⟨n, hn, rfl⟩
    have := QuotientGroup.eq.1 (φ.injective key)
    rw [mem_subgroupOf] at this
    exact this

theorem yamadaL₃_eq_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaL₃ d t = yamadaM₃ d t ⊔ zpowers t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have hL₂L₃ := h.yamadaL₂_le_yamadaL₃ d hNH h561 h562 h591 h592 (h.yamada_5_9_3 d hlay)
    (h.yamada_5_10_1 d hlay) (h.yamada_5_10_2 d hlay)
  have hM₂M₃ : yamadaM₂ d t ≤ yamadaM₃ d t := by
    rw [h.yamadaM₂_eq_inf_centralizer d h591 h592]
    exact inf_le_inf_right _ hL₂L₃
  refine le_antisymm (fun x hx => ?_)
    (sup_le inf_le_left ((zpowers_le).2 (hL₂L₃ (h.t_mem_yamadaL₂ d))))
  obtain ⟨g, hg, hgx⟩ := h.exists_mem_yamadaM₃_inv_mul_mem d hlay hx
  rw [h591.1] at hgx
  have := mul_mem (mem_sup_left hg) (sup_le_sup_right hM₂M₃ _ hgx)
  rwa [mul_inv_cancel_left] at this

theorem t_not_mem_yamadaM₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∉ yamadaM₃ d t := fun ht =>
  t_not_mem_centralizer_yamadaY₂ d (h.yamada_5_9_2 d hlay) (Subgroup.mem_inf.1 ht).2

theorem t_mem_yamadaR₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∈ yamadaR₃ d t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  rw [(h.yamada_5_17_2 d hNH h561 h562 h591 h592 h593 h5101 h5102).2]
  exact mem_sup_left (h.yamadaL₂_le_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101 h5102
    (h.t_mem_yamadaL₂ d))

theorem yamadaR₃_eq_sup (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaR₃ d t = yamadaS₃ d t ⊔ zpowers t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have hR₃ := (h.yamada_5_17_2 d hNH h561 h562 h591 h592 h593 h5101 h5102).2
  have hCV : centralizer (yamadaY₂ d t : Set G) ≤ centralizer (yamadaV₁ d t : Set G) :=
    centralizer_le (yamadaV₁_le_yamadaY₂ d)
  have hM₃S₃ : yamadaM₃ d t ≤ yamadaS₃ d t :=
    le_inf (inf_le_left.trans (hR₃ ▸ le_sup_left)) (inf_le_right.trans hCV)
  have hSS₃ : d.S.map L.subtype ≤ yamadaS₃ d t :=
    le_inf (hR₃ ▸ le_sup_right) (h.S_map_le_centralizer_yamadaV₁ d hlay)
  refine le_antisymm ?_ (sup_le inf_le_left ((zpowers_le).2 (h.t_mem_yamadaR₃ d hlay)))
  rw [hR₃, h.yamadaL₃_eq_sup d hlay]
  exact sup_le (sup_le (hM₃S₃.trans le_sup_left) le_sup_right) (hSS₃.trans le_sup_left)

theorem t_not_mem_yamadaS₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : t ∉ yamadaS₃ d t := fun ht =>
  h.t_not_mem_centralizer_yamadaV₁ d hlay (Subgroup.mem_inf.1 ht).2

end LThree

section CFive

theorem t_mem_yamadaC₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) : t ∈ yamadaC₅ d t :=
  yamadaC₁_le_yamadaC₅ d t (h.t_mem_yamadaC₁ d)

theorem t_mem_normalizer_yamadaS₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    t ∈ normalizer (yamadaS₃ d t : Set G) :=
  mem_normalizer_inf_D4 (le_normalizer (h.t_mem_yamadaR₃ d hlay))
    (mem_normalizer_centralizer_D4 (h.t_mem_normalizer_yamadaV₁ d))

theorem t_mem_normalizer_yamadaD₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    t ∈ normalizer (yamadaD₃ d t : Set G) :=
  mem_normalizer_inf_D4 (h.t_mem_normalizer_yamadaS₃ d hlay)
    (le_normalizer (h.t_mem_yamadaC₅ d))

theorem yamadaR₃_inf_yamadaC₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaR₃ d t ⊓ yamadaC₅ d t = yamadaD₃ d t ⊔ zpowers t := by
  have htC₅ := h.t_mem_yamadaC₅ d
  have hD₃ : yamadaD₃ d t ≤ yamadaR₃ d t ⊓ yamadaC₅ d t := fun x hx =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).1, (Subgroup.mem_inf.1 hx).2⟩
  refine le_antisymm (fun x hx => ?_) (sup_le hD₃
    ((zpowers_le).2 (Subgroup.mem_inf.2 ⟨h.t_mem_yamadaR₃ d hlay, htC₅⟩)))
  obtain ⟨hxR, hxC⟩ := Subgroup.mem_inf.1 hx
  rw [h.yamadaR₃_eq_sup d hlay,
    h.mem_sup_zpowers_iff_of_normalizer (h.t_mem_normalizer_yamadaS₃ d hlay)] at hxR
  rcases hxR with hxS | hxS
  · exact mem_sup_left (Subgroup.mem_inf.2 ⟨hxS, hxC⟩)
  · have h1 : t * x ∈ yamadaD₃ d t := Subgroup.mem_inf.2 ⟨hxS, mul_mem htC₅ hxC⟩
    have e : x = t * (t * x) := by rw [← mul_assoc, h.t_mul_t, one_mul]
    rw [e]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left h1)

theorem mem_yamadaR₃_of_conj_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x w v : G}
    (hx : x ∈ yamadaC₅ d t) (hw : w ∈ d.W.map L.subtype) (hv : v ∈ yamadaV₁ d t)
    (e : x * t * x⁻¹ = t * w * v) : x ∈ yamadaR₃ d t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  refine (h.mem_inf_normalizer_iff d hNH h561 h562 (yamadaW₁_le_yamadaD₁ d)
    (h.yamadaR₅_le_normalizer_yamadaW₁ d hNH h561 h562 h591 h592 h593)).2 ⟨mem_sup_left hx, ?_⟩
  rw [show t * x * t * x⁻¹ = t * (x * t * x⁻¹) by group, e, ← mul_assoc, ← mul_assoc,
    h.t_mul_t, one_mul]
  exact mul_mem (mem_sup_left hw) (mem_sup_right hv)

theorem exists_mul_mem_yamadaC₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} (hx : x ∈ yamadaC₅ d t) :
    ∃ x₁ ∈ yamadaR₃ d t ⊓ yamadaC₅ d t, ∃ x₂ ∈ yamadaR₃ d t ⊓ yamadaC₅ d t,
      (x₁ * (((d.u : L) : G) * x₂ * ((d.u : L) : G)⁻¹))⁻¹ * x ∈ yamadaC₁ d t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  obtain ⟨_, _, φ, hφ, hφeq⟩ := h.yamada_5_12_module d hNH h561 h562 h591 h592 h593
  have hCQ := h.yamadaC₅_eq_yamadaQ₅ d hNH h561 h562 h591 h592 h593
  have hu : ((d.u : L) : G) ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
    Subgroup.mem_inf.2 ⟨h.L_le_centralizer d.u.2, coe_mem_normalizer_map d.u_mem_normalizer_V⟩
  have hD : ∀ w : L, w ∈ d.W → ((w : L) : G) ∈ d.D.map L.subtype := fun w hw =>
    ⟨w, (d.W_le_F.trans d.F_le_D) hw, rfl⟩
  obtain ⟨δ, hδ, hxt⟩ := (h.yamada_5_12 d hNH h561 h562 h591 h592 h593).2.1.1 x hx
  obtain ⟨n, hn, v, hv, rfl⟩ := h.exists_mul_of_mem_yamadaD₁ d h561 h562 hδ
  obtain ⟨n', hn', rfl⟩ := hn
  obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := d.exists_mul_conj_u_of_mem_D hn'
  obtain ⟨x₁, hx₁Q, v₁, hv₁, hx₁t⟩ := h.exists_mem_yamadaQ₅_conj_eq d hNH h561 h562 h591 h592 h593
    (D_le_yamadaD₁ d t (hD w₁ hw₁))
  obtain ⟨x₂, hx₂Q, v₂, hv₂, hx₂t⟩ := h.exists_mem_yamadaQ₅_conj_eq d hNH h561 h562 h591 h592 h593
    (D_le_yamadaD₁ d t (hD w₂ hw₂))
  have hx₁C : x₁ ∈ yamadaC₅ d t := hCQ ▸ hx₁Q
  have hx₂C : x₂ ∈ yamadaC₅ d t := hCQ ▸ hx₂Q
  refine ⟨x₁, Subgroup.mem_inf.2 ⟨h.mem_yamadaR₃_of_conj_eq d hlay hx₁C ⟨w₁, hw₁, rfl⟩ hv₁
    hx₁t, hx₁C⟩, x₂, Subgroup.mem_inf.2 ⟨h.mem_yamadaR₃_of_conj_eq d hlay hx₂C
    ⟨w₂, hw₂, rfl⟩ hv₂ hx₂t, hx₂C⟩, ?_⟩
  have e1 := hφ ⟨x₁, hx₁C⟩ ⟨_, hD w₁ hw₁⟩ ⟨v₁, hv₁, hx₁t⟩
  have e2 := hφ ⟨x₂, hx₂C⟩ ⟨_, hD w₂ hw₂⟩ ⟨v₂, hv₂, hx₂t⟩
  obtain ⟨hux, huδ, e3⟩ := hφeq _ hu ⟨x₂, hx₂C⟩ ⟨_, hD w₂ hw₂⟩ e2
  have e4 := hφ ⟨x, hx⟩ ⟨_, ⟨_, hn', rfl⟩⟩ ⟨v, hv, by rw [hxt]; exact (mul_assoc _ _ _).symm⟩
  have key : φ (QuotientGroup.mk (⟨x₁, hx₁C⟩ * ⟨_, hux⟩)) = φ (QuotientGroup.mk ⟨x, hx⟩) := by
    rw [QuotientGroup.mk_mul, map_mul, e1, e3, e4, ← QuotientGroup.mk_mul]
    congr 1
  have := QuotientGroup.eq.1 (φ.injective key)
  rw [mem_subgroupOf] at this
  exact this

theorem mem_yamadaV₁_of_mem_yamadaW₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {w : G}
    (hw : w ∈ yamadaW₁ d t) (hwu : ((d.u : L) : G)⁻¹ * w * (d.u : G) ∈ yamadaW₁ d t) :
    w ∈ yamadaV₁ d t := by
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have hWV : d.W.map L.subtype ≤ normalizer (yamadaV₁ d t : Set G) := fun g hg =>
    Subgroup.centralizer_le_normalizer _
      (h.S_map_le_centralizer_yamadaV₁ d hlay (map_mono d.W_le_S hg))
  have huV₁ : ((d.u : L) : G) ∈ normalizer (yamadaV₁ d t : Set G) :=
    normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (u_mem_normalizer_yamadaD₁ d h561)
  have hw' : w ∈ ((d.W.map L.subtype ⊔ yamadaV₁ d t : Subgroup G) : Set G) := hw
  have hwu' : ((d.u : L) : G)⁻¹ * w * (d.u : G) ∈
      ((d.W.map L.subtype ⊔ yamadaV₁ d t : Subgroup G) : Set G) := hwu
  rw [coe_mul_of_left_le_normalizer_right _ _ hWV] at hw' hwu'
  obtain ⟨_, ⟨a, ha, rfl⟩, b, hb, e⟩ := hw'
  obtain ⟨_, ⟨a', ha', rfl⟩, b', hb', e'⟩ := hwu'
  simp only [Subgroup.coe_subtype] at e e'
  have hbu : ((d.u : L) : G)⁻¹ * b * (d.u : G) ∈ yamadaV₁ d t := by
    have := (mem_normalizer_iff.1 (inv_mem huV₁) b).1 hb
    rwa [inv_inv] at this
  have huaD : d.u⁻¹ * a * d.u ∈ d.D := by
    have := (mem_normalizer_iff.1 (inv_mem d.u_mem_normalizer_D) a).1
      ((d.W_le_F.trans d.F_le_D) ha)
    rwa [inv_inv] at this
  have hz : ((a'⁻¹ * (d.u⁻¹ * a * d.u) : L) : G) ∈ yamadaV₁ d t ⊓ d.D.map L.subtype := by
    refine Subgroup.mem_inf.2 ⟨?_, ⟨_, mul_mem (inv_mem ((d.W_le_F.trans d.F_le_D) ha')) huaD,
      rfl⟩⟩
    have ha'e : ((a' : L) : G) = ((d.u : L) : G)⁻¹ * w * (d.u : G) * b'⁻¹ := by
      rw [← e']
      group
    have e2 : ((a'⁻¹ * (d.u⁻¹ * a * d.u) : L) : G) =
        b' * (((d.u : L) : G)⁻¹ * b * (d.u : G))⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [ha'e, ← e]
      group
    rw [e2]
    exact mul_mem hb' (inv_mem hbu)
  rw [h.yamadaV₁_inf_D d h562] at hz
  obtain ⟨z, hzV, hze⟩ := hz
  have hzL : z = a'⁻¹ * (d.u⁻¹ * a * d.u) := Subtype.ext hze
  have haW : a ∈ d.W ⊓ d.W.map (MulAut.conj d.u).toMonoidHom := by
    refine Subgroup.mem_inf.2 ⟨ha, ?_⟩
    rw [mem_map_conj_iff_D4]
    have e3 : d.u⁻¹ * a * d.u = a' * z := by
      rw [hzL]
      group
    rw [e3]
    exact mul_mem ha' ((d.V_le_Y.trans d.Y_le_W) hzV)
  rw [d.W_inf_conj_u] at haW
  rw [← e]
  exact mul_mem (V_le_yamadaV₁ d h562 ⟨a, haW, rfl⟩) hb

theorem yamadaD₃_inf_conj_u (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaD₃ d t ⊓ (yamadaD₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom =
      yamadaD₁ d t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h514 := h.yamada_5_14 d hNH h561 h562 h591 h592 h593
  have hCQ := h.yamadaC₅_eq_yamadaQ₅ d hNH h561 h562 h591 h592 h593
  have htV₁ := h.t_not_mem_centralizer_yamadaV₁ d hlay
  have hut : ((d.u : L) : G) * t = t * (d.u : G) :=
    mem_centralizer_singleton_iff.1 (h.L_le_centralizer d.u.2)
  have hut' : ((d.u : L) : G)⁻¹ * t = t * ((d.u : L) : G)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hut, mul_inv_cancel_right]
  have huD₁ := u_mem_normalizer_yamadaD₁ d h561
  have hD₁C₁ : yamadaD₁ d t ≤ yamadaC₁ d t := by
    rw [h561.1]
    exact le_sup_left
  have hD₁D₃ : yamadaD₁ d t ≤ yamadaD₃ d t := fun y hy =>
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨h514.2.2.2.1.1 (h.yamadaC₁_le_yamadaR₂ d (hD₁C₁ hy)),
      yamadaD₁_le_centralizer_yamadaV₁ d hy⟩, yamadaC₁_le_yamadaC₅ d t (hD₁C₁ hy)⟩
  refine le_antisymm (fun x hx => ?_) (le_inf hD₁D₃ fun y hy => ?_)
  · obtain ⟨hx₁, hx₂⟩ := Subgroup.mem_inf.1 hx
    rw [mem_map_conj_iff_D4] at hx₂
    have hxR : x ∈ yamadaR₃ d t := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx₁).1).1
    have hxV : x ∈ centralizer (yamadaV₁ d t : Set G) :=
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx₁).1).2
    have hxC : x ∈ yamadaC₅ d t := (Subgroup.mem_inf.1 hx₁).2
    have hx'R : ((d.u : L) : G)⁻¹ * x * (d.u : G) ∈ yamadaR₃ d t :=
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx₂).1).1
    obtain ⟨w, hw, hxt⟩ := h514.1.1 x hxR
    obtain ⟨w', hw', hxt'⟩ := h514.1.1 _ hx'R
    have hutu : ((d.u : L) : G) * t * ((d.u : L) : G)⁻¹ = t := by rw [hut, mul_inv_cancel_right]
    have e1 : ((d.u : L) : G)⁻¹ * x * (d.u : G) * t * (((d.u : L) : G)⁻¹ * x * (d.u : G))⁻¹ =
        t * (((d.u : L) : G)⁻¹ * w * (d.u : G)) := by
      calc ((d.u : L) : G)⁻¹ * x * (d.u : G) * t * (((d.u : L) : G)⁻¹ * x * (d.u : G))⁻¹ =
          ((d.u : L) : G)⁻¹ * x * (((d.u : L) : G) * t * ((d.u : L) : G)⁻¹) * x⁻¹ *
            (d.u : G) := by group
        _ = ((d.u : L) : G)⁻¹ * (x * t * x⁻¹) * (d.u : G) := by rw [hutu]; group
        _ = (((d.u : L) : G)⁻¹ * t) * w * (d.u : G) := by rw [hxt]; group
        _ = t * (((d.u : L) : G)⁻¹ * w * (d.u : G)) := by rw [hut']; group
    rw [e1] at hxt'
    have hww := mul_left_cancel hxt'
    have hwV : w ∈ yamadaV₁ d t := h.mem_yamadaV₁_of_mem_yamadaW₁ d hlay hw (hww ▸ hw')
    have hxC₁ : x ∈ yamadaC₁ d t := by
      refine h.mem_yamadaC₁_of_crossed_mem d hNH h561 h562 (hCQ ▸ hxC) ?_
      rw [show t * x * t * x⁻¹ = t * (x * t * x⁻¹) by group, hxt, ← mul_assoc, h.t_mul_t,
        one_mul]
      exact hwV
    rw [h561.1, h.mem_sup_zpowers_iff_of_normalizer (h.t_mem_normalizer_yamadaD₁ d)] at hxC₁
    rcases hxC₁ with h1 | h1
    · exact h1
    · exfalso
      apply htV₁
      have := mul_mem (yamadaD₁_le_centralizer_yamadaV₁ d h1) (inv_mem hxV)
      rwa [mul_inv_cancel_right] at this
  · rw [mem_map_conj_iff_D4]
    apply hD₁D₃
    have := (mem_normalizer_iff.1 (inv_mem huD₁) y).1 hy
    rwa [inv_inv] at this

theorem yamada_5_20 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaC₅ d t = yamadaD₅ d t ⊔ zpowers t ∧ t ∉ yamadaD₅ d t ∧
      yamadaD₅ d t = yamadaD₃ d t ⊔
        (yamadaD₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom ∧
      yamadaD₃ d t ⊓ (yamadaD₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom =
        yamadaD₁ d t ∧
      yamadaL₃ d t = yamadaM₃ d t ⊔ zpowers t ∧ t ∉ yamadaM₃ d t ∧
      yamadaR₃ d t = yamadaS₃ d t ⊔ zpowers t ∧ t ∉ yamadaS₃ d t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have htC₅ := h.t_mem_yamadaC₅ d
  have htV₁ := h.t_not_mem_centralizer_yamadaV₁ d hlay
  have htD₃ := h.t_mem_normalizer_yamadaD₃ d hlay
  have hTD₃ := h.yamadaR₃_inf_yamadaC₅ d hlay
  have hu : ((d.u : L) : G) ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
    Subgroup.mem_inf.2 ⟨h.L_le_centralizer d.u.2, coe_mem_normalizer_map d.u_mem_normalizer_V⟩
  have hut : ((d.u : L) : G) * t = t * (d.u : G) :=
    mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hu).1
  have hut' : ((d.u : L) : G)⁻¹ * t = t * ((d.u : L) : G)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hut, mul_inv_cancel_right]
  have huC₅ : ((d.u : L) : G) ∈ normalizer (yamadaC₅ d t : Set G) :=
    le_normalizer_yamadaC₅ d t (le_normalizer_yamadaC₁ d t (h.centralizer_inf_normalizer_V_le d hu))
  have huV₁ : ((d.u : L) : G) ∈ normalizer (yamadaV₁ d t : Set G) :=
    normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (u_mem_normalizer_yamadaD₁ d h561)
  have huD₅ : ((d.u : L) : G) ∈ normalizer (yamadaD₅ d t : Set G) :=
    mem_normalizer_inf_D4 huC₅ (mem_normalizer_centralizer_D4 huV₁)
  have hD₃D₅ : yamadaD₃ d t ≤ yamadaD₅ d t := fun x hx =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2,
      (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).2⟩
  have hD₃uD₅ : (yamadaD₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom ≤
      yamadaD₅ d t := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.1 huD₅ y).1 (hD₃D₅ hy)
  set K := yamadaD₃ d t ⊔ (yamadaD₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom with hK
  have hKD₅ : K ≤ yamadaD₅ d t := sup_le hD₃D₅ hD₃uD₅
  have htK : t ∈ normalizer (K : Set G) := by
    refine mem_normalizer_sup htD₃ (mem_normalizer_fintype fun y hy => ?_)
    rw [SetLike.mem_coe, mem_map_conj_iff_D4] at hy ⊢
    have e : ((d.u : L) : G)⁻¹ * (t * y * t⁻¹) * (d.u : G) =
        t * (((d.u : L) : G)⁻¹ * y * (d.u : G)) * t⁻¹ := by
      calc ((d.u : L) : G)⁻¹ * (t * y * t⁻¹) * (d.u : G) =
          (((d.u : L) : G)⁻¹ * t) * y * (((d.u : L) : G)⁻¹ * t)⁻¹ := by group
        _ = (t * ((d.u : L) : G)⁻¹) * y * (t * ((d.u : L) : G)⁻¹)⁻¹ := by rw [hut']
        _ = t * (((d.u : L) : G)⁻¹ * y * (d.u : G)) * t⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 htD₃ _).1 hy
  have hTK : ∀ y ∈ yamadaR₃ d t ⊓ yamadaC₅ d t, y ∈ K ⊔ zpowers t := fun y hy => by
    rw [hTD₃] at hy
    exact (sup_le_sup_right (le_sup_left : yamadaD₃ d t ≤ K) (zpowers t)) hy
  have hTuK : ∀ y ∈ yamadaR₃ d t ⊓ yamadaC₅ d t,
      ((d.u : L) : G) * y * ((d.u : L) : G)⁻¹ ∈ K ⊔ zpowers t := fun y hy => by
    rw [hTD₃, h.mem_sup_zpowers_iff_of_normalizer htD₃] at hy
    rcases hy with hy | hy
    · exact mem_sup_left (mem_sup_right ⟨y, hy, rfl⟩)
    · have h1 : t * (((d.u : L) : G) * y * ((d.u : L) : G)⁻¹) ∈ K := by
        have e : t * (((d.u : L) : G) * y * ((d.u : L) : G)⁻¹) =
            (MulAut.conj ((d.u : L) : G)).toMonoidHom (t * y) := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          calc t * (((d.u : L) : G) * y * ((d.u : L) : G)⁻¹) =
              (t * (d.u : G)) * y * ((d.u : L) : G)⁻¹ := by group
            _ = (((d.u : L) : G) * t) * y * ((d.u : L) : G)⁻¹ := by rw [hut]
            _ = ((d.u : L) : G) * (t * y) * ((d.u : L) : G)⁻¹ := by group
        rw [e]
        exact mem_sup_right ⟨_, hy, rfl⟩
      have e : ((d.u : L) : G) * y * ((d.u : L) : G)⁻¹ =
          t * (t * (((d.u : L) : G) * y * ((d.u : L) : G)⁻¹)) := by
        rw [← mul_assoc, h.t_mul_t, one_mul]
      rw [e]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left h1)
  have hC₁T : yamadaC₁ d t ≤ yamadaR₃ d t ⊓ yamadaC₅ d t :=
    le_inf ((h.yamadaC₁_le_yamadaR₂ d).trans
      (h.yamada_5_14 d hNH h561 h562 h591 h592 h593).2.2.2.1.1) (yamadaC₁_le_yamadaC₅ d t)
  have hC₅K : yamadaC₅ d t ≤ K ⊔ zpowers t := fun x hx => by
    obtain ⟨x₁, hx₁, x₂, hx₂, hc⟩ := h.exists_mul_mem_yamadaC₁ d hlay hx
    have e : x = x₁ * (((d.u : L) : G) * x₂ * ((d.u : L) : G)⁻¹) *
        ((x₁ * (((d.u : L) : G) * x₂ * ((d.u : L) : G)⁻¹))⁻¹ * x) := by group
    rw [e]
    exact mul_mem (mul_mem (hTK x₁ hx₁) (hTuK x₂ hx₂)) (hTK _ (hC₁T hc))
  have hD₅K : yamadaD₅ d t ≤ K := fun x hx => by
    have h1 := hC₅K (Subgroup.mem_inf.1 hx).1
    rw [h.mem_sup_zpowers_iff_of_normalizer htK] at h1
    rcases h1 with h1 | h1
    · exact h1
    · exfalso
      apply htV₁
      have := mul_mem (Subgroup.mem_inf.1 (hKD₅ h1)).2 (inv_mem (Subgroup.mem_inf.1 hx).2)
      rwa [mul_inv_cancel_right] at this
  have hD₅eq : yamadaD₅ d t = K := le_antisymm hD₅K hKD₅
  refine ⟨le_antisymm (hD₅eq ▸ hC₅K) (sup_le inf_le_left ((zpowers_le).2 htC₅)),
    fun ht => htV₁ (Subgroup.mem_inf.1 ht).2, hD₅eq, h.yamadaD₃_inf_conj_u d hlay,
    h.yamadaL₃_eq_sup d hlay, h.t_not_mem_yamadaM₃ d hlay, h.yamadaR₃_eq_sup d hlay,
    h.t_not_mem_yamadaS₃ d hlay⟩

end CFive

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
