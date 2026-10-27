module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S3D
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S3C

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem V₃_le_R₃ : d.V₃ ≤ d.R₃ := V₃_le_S₃.trans S₃_le_R₃

theorem V₃_le_D₂ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    d.V₃ ≤ d.D₂ := by
  rw [h.V₃_eq hK]
  exact sup_le inf_le_right h.Y_le_D₂

theorem D₂_le_normalizer_V₃ (h : d.Hyp) : d.D₂ ≤ normalizer (d.V₃ : Set G) := fun e he =>
  mem_normalizer_fintype fun x hx => by
    obtain ⟨hxS, hxc⟩ := (h.mem_V₃_iff).1 hx
    have heN := h.D₂_le_normalizer_S₃ he
    refine (h.mem_V₃_iff).2 ⟨(mem_normalizer_iff.1 heN x).1 hxS, fun s hs => ?_⟩
    have hs' : e⁻¹ * s * e ∈ d.S₃ := by
      have := (mem_normalizer_iff.1 (inv_mem heN) s).1 hs
      rwa [inv_inv] at this
    have hY : e ∈ normalizer (d.Y : Set G) :=
      mem_normalizer_of_forall_comm fun y hy => (D₂_comm_Y' he hy).symm
    have := (mem_normalizer_iff.1 hY _).1 (hxc _ hs')
    rwa [show e * (x * (e⁻¹ * s * e) * x⁻¹ * (e⁻¹ * s * e)⁻¹) * e⁻¹ =
      e * x * e⁻¹ * s * (e * x * e⁻¹)⁻¹ * s⁻¹ by group] at this

theorem conj_v_mem_D₂ (h : d.Hyp) {x : G} (hx : x ∈ d.D₂) : d.v⁻¹ * x * d.v ∈ d.D₂ := by
  have := h.conj_mem_D₂ (inv_mem h.v_mem_XC₀) hx
  rwa [inv_inv] at this

theorem conj_V₃_le_D₂ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    d.V₃.map (MulAut.conj d.v).toMonoidHom ≤ d.D₂ := fun x hx => by
  have hx' := (mem_map_conj_iff _ _ _).1 hx
  have := h.conj_mem_D₂ h.v_mem_XC₀ (h.V₃_le_D₂ hK hx')
  rwa [show d.v * (d.v⁻¹ * x * d.v) * d.v⁻¹ = x by group] at this

theorem V₃_inf_conj_V₃ (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    d.V₃ ⊓ d.V₃.map (MulAut.conj d.v).toMonoidHom = d.Y := by
  have hvN := h.v_mem_NHA₂
  have hvY : ∀ y ∈ d.Y, d.v⁻¹ * y * d.v ∈ d.Y := fun y hy => by
    have := (mem_normalizer_iff.1 (inv_mem (h.NHA₂_le_normalizer_Y hvN)) y).1 hy
    rwa [inv_inv] at this
  refine le_antisymm (fun x hx => ?_) (le_inf h.Y_le_V₃ fun y hy =>
    (mem_map_conj_iff _ _ _).2 (h.Y_le_V₃ (hvY y hy)))
  obtain ⟨hxV, hxv⟩ := Subgroup.mem_inf.1 hx
  have hxv' : d.v⁻¹ * x * d.v ∈ d.V₃ := (mem_map_conj_iff _ _ _).1 hxv
  have hxD₀ : x ∈ d.D₀ := by
    have : x ∈ d.R₃ ⊓ d.R₃.map (MulAut.conj d.v).toMonoidHom ⊓ d.D₂ :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨V₃_le_R₃ hxV,
        (mem_map_conj_iff _ _ _).2 (V₃_le_R₃ hxv')⟩, h.V₃_le_D₂ hK hxV⟩
    rwa [h.R₃_inf_conj_inf_D₂] at this
  rw [h.D₀_eq] at hxD₀
  obtain ⟨a, ha, e, he, hae⟩ := (h.mem_A₂E₂_iff).1 hxD₀
  have heY : e ∈ d.Y := h.Y_eq_E₂ ▸ he
  have hvA : d.v⁻¹ * a * d.v ∈ d.A₂ := by
    have := (mem_normalizer_iff.1 (inv_mem hvN.1) a).1 ha
    rwa [inv_inv] at this
  have haS' : a ∈ ⁅d.S, d.S⁆ :=
    h.mem_commutator_S_of_mul_mem_V₃ (d.A₂_le_S ha) heY (hae ▸ hxV)
  have hvaS' : d.v⁻¹ * a * d.v ∈ ⁅d.S, d.S⁆ := by
    refine h.mem_commutator_S_of_mul_mem_V₃ (d.A₂_le_S hvA) (hvY e heY) ?_
    rw [show d.v⁻¹ * a * d.v * (d.v⁻¹ * e * d.v) = d.v⁻¹ * (a * e) * d.v by group, ← hae]
    exact hxv'
  have haF : a ∈ d.F := by
    rw [commutator_S_eq] at haS' hvaS'
    exact h.mem_F_of_mem_X₄F_of_conj_v ha haS' hvaS'
  rw [hae]
  exact mul_mem (h.F_le_Y haF) heY

theorem card_conj_V₃ : Nat.card (d.V₃.map (MulAut.conj d.v).toMonoidHom) = Nat.card d.V₃ :=
  Subgroup.card_map_of_injective (MulAut.conj d.v).injective

theorem D₂_eq_V₃_sup (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) :
    d.D₂ = d.V₃ ⊔ d.V₃.map (MulAut.conj d.v).toMonoidHom := by
  have hN : d.V₃.map (MulAut.conj d.v).toMonoidHom ≤ normalizer (d.V₃ : Set G) :=
    (h.conj_V₃_le_D₂ hK).trans h.D₂_le_normalizer_V₃
  have e := card_sup_mul_card_inf_of_le_normalizer d.V₃ _ hN
  rw [h.V₃_inf_conj_V₃ hK, card_conj_V₃, h.card_V₃ hK, h.card_Y'] at e
  refine (Subgroup.eq_of_le_of_card_ge (sup_le (h.V₃_le_D₂ hK) (h.conj_V₃_le_D₂ hK)) ?_).symm
  rw [h.card_D₂]
  omega

theorem pull_commutator_Ssub : d.pull (⁅Ssub, Ssub⁆ : Subgroup SU52) = ⁅d.S, d.S⁆ :=
  Subgroup.map_commutator Ssub Ssub d.ι

theorem commutator_commutator_S : ⁅⁅d.S, d.S⁆, ⁅d.S, d.S⁆⁆ = d.ZX₄ := by
  rw [← pull_commutator_Ssub (d := d), Data.ZX₄, ← commutator_commutator_Ssub]
  exact (Subgroup.map_commutator (⁅Ssub, Ssub⁆) (⁅Ssub, Ssub⁆) d.ι).symm

theorem mem_F_of_comm_commutator_S {a : G} (ha : a ∈ d.S)
    (hc : ∀ s ∈ ⁅d.S, d.S⁆, a * s = s * a) : a ∈ d.F := by
  obtain ⟨α, hα, rfl⟩ := ha
  have h1 : α ∈ Ssub ⊓ centralizer ((⁅Ssub, Ssub⁆ : Subgroup SU52) : Set SU52) := by
    refine Subgroup.mem_inf.2 ⟨hα, mem_centralizer_iff.2 fun σ hσ => ?_⟩
    have hσ' : d.ι σ ∈ ⁅d.S, d.S⁆ := by
      rw [← pull_commutator_Ssub]
      exact ⟨σ, hσ, rfl⟩
    have := hc _ hσ'
    exact d.ι_injective (by rw [map_mul, map_mul]; exact this.symm)
  rw [Ssub_inf_centralizer_commutator_Ssub] at h1
  exact ⟨α, h1, rfl⟩

theorem V₃_commutator_mem_W (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) {x y : G} (hx : x ∈ d.V₃)
    (hy : y ∈ d.V₃) : x * y * x⁻¹ * y⁻¹ ∈ d.W := by
  have hV := h.V₃_eq hK
  have hTD₁ : d.D₃ ⊓ d.D₂ ≤ d.D₁ := fun t ht => D₃_le_D₁' (Subgroup.mem_inf.1 ht).1
  have hTD₂ : d.D₃ ⊓ d.D₂ ≤ d.D₂ := inf_le_right
  have hYW : ∀ y ∈ d.Y, y ∈ normalizer (d.W : Set G) := fun y hy =>
    mem_normalizer_of_forall_comm fun w hw => h.Y_comm (d.W_le_Y hw) hy
  have hYcV : ∀ y ∈ d.Y, ∀ v ∈ d.V₃, v * y = y * v := fun y hy v hv => by
    have hle : d.V₃ ≤ centralizer ({y} : Set G) := by
      rw [hV]
      exact sup_le (fun t ht => mem_centralizer_singleton_iff.2 (D₂_comm_Y' (hTD₂ ht) hy))
        (fun y' hy' => mem_centralizer_singleton_iff.2 (h.Y_comm hy' hy))
    exact mem_centralizer_singleton_iff.1 (hle hv)
  have hTN : ∀ t ∈ d.D₃ ⊓ d.D₂, t ∈ normalizer (d.W : Set G) := fun t ht =>
    mem_normalizer_of_forall_comm fun w hw =>
      mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hTD₁ ht)).2 w hw
  have hTc : d.D₃ ⊓ d.D₂ ≤ cenMod d.W d.V₃ := fun t ht => by
    have hle : d.V₃ ≤ centModSub d.W t := by
      rw [hV]
      refine sup_le (fun t' ht' => mem_centModSub.2 ⟨hTN t' ht',
        h.D₁_commutator_mem_W hK (hTD₁ ht') (hTD₁ ht)⟩) (fun y hy => ?_)
      refine mem_centModSub.2 ⟨hYW y hy, ?_⟩
      rw [← D₂_comm_Y' (hTD₂ ht) hy, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
    refine ⟨hTN t ht, fun m hm => ?_⟩
    have := inv_mem (mem_centModSub.1 (hle hm)).2
    rwa [show (m * t * m⁻¹ * t⁻¹)⁻¹ = t * m * t⁻¹ * m⁻¹ by group] at this
  have hYc : d.Y ≤ cenMod d.W d.V₃ := fun y hy =>
    ⟨hYW y hy, fun m hm => by
      rw [← hYcV y hy m hm, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _⟩
  have hall : d.V₃ ≤ cenMod d.W d.V₃ := hV.le.trans (sup_le hTc hYc)
  exact (hall hx).2 y hy

theorem commutator_V₃_eq_W (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) : ⁅d.V₃, d.V₃⁆ = d.W := by
  have hCW : ⁅d.V₃, d.V₃⁆ ≤ d.W := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact h.V₃_commutator_mem_W hK hx hy
  refine le_antisymm hCW ?_
  by_contra hWC
  set C : Subgroup G := ⁅d.V₃, d.V₃⁆ with hC
  have hS'V : ⁅d.S, d.S⁆ ≤ d.V₃ := fun x hx => by
    have : x ∈ d.S ⊓ d.V₃ := by
      rw [h.S_inf_V₃]
      exact hx
    exact this.2
  have hZC : d.ZX₄ ≤ C := by
    rw [← commutator_commutator_S]
    exact Subgroup.commutator_mono hS'V hS'V
  have hZ : Nat.card d.ZX₄ = 2 := by rw [Data.ZX₄, d.card_pull, card_ZX₄sub]
  have hW4 : Nat.card d.W = 4 := h.sec4_9_W.1
  have hd1 : Nat.card C ∣ 4 := hW4 ▸ Subgroup.card_dvd_of_le hCW
  have hd2 : 2 ∣ Nat.card C := hZ ▸ Subgroup.card_dvd_of_le hZC
  have hne4 : Nat.card C ≠ 4 := fun e => hWC (Subgroup.eq_of_le_of_card_ge hCW (by omega) ▸ le_rfl)
  have hle4 : Nat.card C ≤ 4 := Nat.le_of_dvd (by norm_num) hd1
  have hpos : 0 < Nat.card C := Nat.card_pos
  have hCZ : C ≤ d.ZX₄ := (Subgroup.eq_of_le_of_card_ge hZC (by omega)).symm.le
  have hZS' : d.ZX₄ ≤ ⁅d.S, d.S⁆ := by
    rw [commutator_S_eq]
    exact (d.pull_mono ZX₄sub_le_X₄sub).trans le_sup_left
  have hNS' : ∀ x ∈ d.V₃, ∀ s ∈ ⁅d.S, d.S⁆, x * s * x⁻¹ ∈ ⁅d.S, d.S⁆ := fun x hx s hs => by
    have hc : x * s * x⁻¹ * s⁻¹ ∈ d.ZX₄ := hCZ (commutator_mem_commutator hx (hS'V hs) |>
      fun h' => by rwa [commutatorElement_def] at h')
    rw [show x * s * x⁻¹ = (x * s * x⁻¹ * s⁻¹) * s by group]
    exact mul_mem (hZS' hc) hs
  have hθY : ∀ x ∈ d.V₃, x * d.t * x⁻¹ * d.t ∈ d.Y := fun x hx => by
    have hxD₂ := h.V₃_le_D₂ hK hx
    have hθD₀ : x * d.t * x⁻¹ * d.t ∈ d.D₀ := h.crossed_mem_D₀ (D₂_le_XC₀ hxD₂)
    rw [h.D₀_eq] at hθD₀
    obtain ⟨a, ha, e, he, hae⟩ := (h.mem_A₂E₂_iff).1 hθD₀
    have heY : e ∈ d.Y := h.Y_eq_E₂ ▸ he
    have haF : a ∈ d.F := by
      refine mem_F_of_comm_commutator_S (d.A₂_le_S ha) fun s hs => ?_
      have hsA : s ∈ d.A₂ := commutator_S_le_A₂ hs
      have hsL : s ∈ d.L := d.pull_le_L _ (d.A₂_le_S hsA)
      have hs₁ : x⁻¹ * s * x ∈ ⁅d.S, d.S⁆ := by
        have := hNS' x⁻¹ (inv_mem hx) s hs
        rwa [inv_inv] at this
      have hs₁L : x⁻¹ * s * x ∈ d.L :=
        d.pull_le_L _ (d.A₂_le_S (commutator_S_le_A₂ hs₁))
      have hts : d.t * s = s * d.t := (h.t_comm_of_mem_L hsL).symm
      have hts₁ : d.t * (x⁻¹ * s * x) = (x⁻¹ * s * x) * d.t := (h.t_comm_of_mem_L hs₁L).symm
      have hθs : (x * d.t * x⁻¹ * d.t) * s = s * (x * d.t * x⁻¹ * d.t) := by
        calc (x * d.t * x⁻¹ * d.t) * s = x * d.t * x⁻¹ * (d.t * s) := by group
          _ = x * d.t * x⁻¹ * (s * d.t) := by rw [hts]
          _ = x * (d.t * (x⁻¹ * s * x)) * x⁻¹ * d.t := by group
          _ = x * ((x⁻¹ * s * x) * d.t) * x⁻¹ * d.t := by rw [hts₁]
          _ = s * (x * d.t * x⁻¹ * d.t) := by group
      rw [hae] at hθs
      have hes : e * s = s * e := Y_comm_D₀ heY (h.A₂_le_D₀ hsA)
      have : (a * s) * e = (s * a) * e := by
        calc (a * s) * e = a * (s * e) := by group
          _ = a * (e * s) := by rw [hes]
          _ = (a * e) * s := by group
          _ = s * (a * e) := hθs
          _ = (s * a) * e := by group
      exact mul_right_cancel this
    rw [hae]
    exact mul_mem (h.F_le_Y haF) heY
  have hVD₀ : d.V₃ ≤ d.D₀ := fun x hx =>
    h.mem_D₀_of_mem_D₂_of_crossed_mem (h.V₃_le_D₂ hK hx) (hθY x hx)
  have hVD : d.V₃ = d.D₀ := Subgroup.eq_of_le_of_card_ge hVD₀ (by
    rw [h.card_D₀, h.card_V₃ hK])
  have hA₂S' : d.A₂ ≤ ⁅d.S, d.S⁆ := by
    intro a ha
    have : a ∈ d.S ⊓ d.V₃ := Subgroup.mem_inf.2 ⟨d.A₂_le_S ha, hVD ▸ h.A₂_le_D₀ ha⟩
    rwa [h.S_inf_V₃] at this
  have := Subgroup.card_le_of_le hA₂S'
  rw [d.card_A₂, card_commutator_S] at this
  omega

theorem V₃_mul_self_mem_Y (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    {x : G} (hx : x ∈ d.V₃) : x * x ∈ d.Y := by
  have hV := h.V₃_eq hK
  have hTN : d.D₃ ⊓ d.D₂ ≤ normalizer (d.Y : Set G) := fun t ht =>
    mem_normalizer_of_forall_comm fun y hy => (D₂_comm_Y' (Subgroup.mem_inf.1 ht).2 hy).symm
  have hset := coe_mul_of_left_le_normalizer_right (d.D₃ ⊓ d.D₂) d.Y hTN
  obtain ⟨t, ht, y, hy, rfl⟩ : x ∈ ((d.D₃ ⊓ d.D₂ : Subgroup G) : Set G) * (d.Y : Set G) := by
    rw [← hset, ← hV]
    exact hx
  have hty : y * t = t * y := (D₂_comm_Y' (Subgroup.mem_inf.1 ht).2 hy).symm
  have e : t * y * (t * y) = (t * t) * (y * y) := by
    calc t * y * (t * y) = t * (y * t) * y := by group
      _ = t * (t * y) * y := by rw [hty]
      _ = (t * t) * (y * y) := by group
  rw [e, h.Y_sq hy, mul_one]
  exact d.W_le_Y (h.D₁_mul_self_mem_W hK (D₃_le_D₁' (Subgroup.mem_inf.1 ht).1))

theorem conj_V₃_mul_self_mem_Y (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) {x : G}
    (hx : x ∈ d.V₃.map (MulAut.conj d.v).toMonoidHom) : x * x ∈ d.Y := by
  have h1 := h.V₃_mul_self_mem_Y hK ((mem_map_conj_iff _ _ _).1 hx)
  have h2 := (mem_normalizer_iff.1 (h.NHA₂_le_normalizer_Y h.v_mem_NHA₂) _).1 h1
  rwa [show d.v * (d.v⁻¹ * x * d.v * (d.v⁻¹ * x * d.v)) * d.v⁻¹ = x * x by group] at h2

theorem D₂_le_normalizer_conj_V₃ (h : d.Hyp) :
    d.D₂ ≤ normalizer ((d.V₃.map (MulAut.conj d.v).toMonoidHom : Subgroup G) : Set G) :=
  fun e he => mem_normalizer_fintype fun x hx => by
    have hx' := (mem_map_conj_iff _ _ _).1 hx
    refine (mem_map_conj_iff _ _ _).2 ?_
    have := (mem_normalizer_iff.1 (h.D₂_le_normalizer_V₃ (h.conj_v_mem_D₂ he)) _).1 hx'
    rwa [show d.v⁻¹ * (e * x * e⁻¹) * d.v =
      (d.v⁻¹ * e * d.v) * (d.v⁻¹ * x * d.v) * (d.v⁻¹ * e * d.v)⁻¹ by group]

theorem commutator_V₃_conj_mem_Y (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) {a b : G} (ha : a ∈ d.V₃)
    (hb : b ∈ d.V₃.map (MulAut.conj d.v).toMonoidHom) : a * b * a⁻¹ * b⁻¹ ∈ d.Y := by
  have h1 : a * b * a⁻¹ ∈ d.V₃.map (MulAut.conj d.v).toMonoidHom :=
    (mem_normalizer_iff.1 (h.D₂_le_normalizer_conj_V₃ (h.V₃_le_D₂ hK ha)) b).1 hb
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ d.V₃.map (MulAut.conj d.v).toMonoidHom := mul_mem h1 (inv_mem hb)
  have h3 : b * a⁻¹ * b⁻¹ ∈ d.V₃ :=
    (mem_normalizer_iff.1 (h.D₂_le_normalizer_V₃ (h.conj_V₃_le_D₂ hK hb)) a⁻¹).1 (inv_mem ha)
  have : a * b * a⁻¹ * b⁻¹ ∈ d.V₃ ⊓ d.V₃.map (MulAut.conj d.v).toMonoidHom :=
    Subgroup.mem_inf.2 ⟨by
      rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
      exact mul_mem ha h3, h2⟩
  rwa [h.V₃_inf_conj_V₃ hK] at this

theorem D₂_commutator_mem_Y (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) {x y : G} (hx : x ∈ d.D₂)
    (hy : y ∈ d.D₂) : x * y * x⁻¹ * y⁻¹ ∈ d.Y := by
  have hD := h.D₂_eq_V₃_sup hK
  have hVc : ∀ a ∈ d.V₃, ∀ a' ∈ d.V₃, a * a' * a⁻¹ * a'⁻¹ ∈ d.Y := fun a ha a' ha' =>
    d.W_le_Y (h.V₃_commutator_mem_W hK ha ha')
  have hV'c : ∀ b ∈ d.V₃.map (MulAut.conj d.v).toMonoidHom,
      ∀ b' ∈ d.V₃.map (MulAut.conj d.v).toMonoidHom, b * b' * b⁻¹ * b'⁻¹ ∈ d.Y :=
    fun b hb b' hb' => by
      have h1 := d.W_le_Y (h.V₃_commutator_mem_W hK ((mem_map_conj_iff _ _ _).1 hb)
        ((mem_map_conj_iff _ _ _).1 hb'))
      have h2 := (mem_normalizer_iff.1 (h.NHA₂_le_normalizer_Y h.v_mem_NHA₂) _).1 h1
      rwa [show d.v * ((d.v⁻¹ * b * d.v) * (d.v⁻¹ * b' * d.v) * (d.v⁻¹ * b * d.v)⁻¹ *
        (d.v⁻¹ * b' * d.v)⁻¹) * d.v⁻¹ = b * b' * b⁻¹ * b'⁻¹ by group] at h2
  have hYN : ∀ x ∈ d.D₂, x ∈ normalizer (d.Y : Set G) := fun x hx =>
    mem_normalizer_of_forall_comm fun y hy => (D₂_comm_Y' hx hy).symm
  have hle : d.V₃ ⊔ d.V₃.map (MulAut.conj d.v).toMonoidHom ≤ cenMod d.Y d.D₂ := by
    refine sup_le (fun a ha => ⟨hYN a (h.V₃_le_D₂ hK ha), fun y hy => ?_⟩)
      (fun b hb => ⟨hYN b (h.conj_V₃_le_D₂ hK hb), fun y hy => ?_⟩)
    · have hle2 : d.D₂ ≤ centModSub d.Y a := hD.le.trans (sup_le
        (fun a' ha' => mem_centModSub.2 ⟨hYN a' (h.V₃_le_D₂ hK ha'), hVc a' ha' a ha⟩)
        (fun b hb => mem_centModSub.2 ⟨hYN b (h.conj_V₃_le_D₂ hK hb), by
          have := inv_mem (h.commutator_V₃_conj_mem_Y hK ha hb)
          rwa [show (a * b * a⁻¹ * b⁻¹)⁻¹ = b * a * b⁻¹ * a⁻¹ by group] at this⟩))
      have := inv_mem (mem_centModSub.1 (hle2 hy)).2
      rwa [show (y * a * y⁻¹ * a⁻¹)⁻¹ = a * y * a⁻¹ * y⁻¹ by group] at this
    · have hle2 : d.D₂ ≤ centModSub d.Y b := hD.le.trans (sup_le
        (fun a' ha' => mem_centModSub.2 ⟨hYN a' (h.V₃_le_D₂ hK ha'),
          h.commutator_V₃_conj_mem_Y hK ha' hb⟩)
        (fun b' hb' => mem_centModSub.2 ⟨hYN b' (h.conj_V₃_le_D₂ hK hb'), hV'c b' hb' b hb⟩))
      have := inv_mem (mem_centModSub.1 (hle2 hy)).2
      rwa [show (y * b * y⁻¹ * b⁻¹)⁻¹ = b * y * b⁻¹ * y⁻¹ by group] at this
  exact ((hD.le.trans hle) hx).2 y hy

theorem D₂_mul_self_mem_Y (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) {x : G} (hx : x ∈ d.D₂) :
    x * x ∈ d.Y := by
  have hD := h.D₂_eq_V₃_sup hK
  have hN : d.V₃.map (MulAut.conj d.v).toMonoidHom ≤ normalizer (d.V₃ : Set G) :=
    (h.conj_V₃_le_D₂ hK).trans h.D₂_le_normalizer_V₃
  have hset := coe_mul_of_left_le_normalizer_right (d.V₃.map (MulAut.conj d.v).toMonoidHom) d.V₃
    hN
  obtain ⟨b, hb, a, ha, rfl⟩ :
      x ∈ ((d.V₃.map (MulAut.conj d.v).toMonoidHom : Subgroup G) : Set G) * (d.V₃ : Set G) := by
    rw [← hset, sup_comm, ← hD]
    exact hx
  have haD := h.V₃_le_D₂ hK ha
  have hbD := h.conj_V₃_le_D₂ hK hb
  have hc := h.D₂_commutator_mem_Y hK haD hbD
  have hbc : b * (a * b * a⁻¹ * b⁻¹) * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by
    rw [D₂_comm_Y' hbD hc, mul_inv_cancel_right]
  have e : b * a * (b * a) = (b * (a * b * a⁻¹ * b⁻¹) * b⁻¹) * (b * b) * (a * a) := by group
  rw [e, hbc]
  exact mul_mem (mul_mem hc (h.conj_V₃_mul_self_mem_Y hK hb)) (h.V₃_mul_self_mem_Y hK ha)

theorem F_le_commutator_A₂ : d.F ≤ ⁅d.A₂, d.A₂⁆ := by
  intro f hf
  obtain ⟨φ, hφ, rfl⟩ := hf
  have : Fsub ≤ (⁅d.A₂, d.A₂⁆).comap d.ι := by
    rw [← closure_genFSU, closure_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨a, ha, b, hb, e⟩ := exists_genFSU_eq_commutator j
    show d.ι (genFSU j) ∈ ⁅d.A₂, d.A₂⁆
    rw [e, map_commutatorElement]
    exact commutator_mem_commutator ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  exact this hφ

theorem commutator_D₂_eq_Y (h : d.Hyp)
    (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W) : ⁅d.D₂, d.D₂⁆ = d.Y := by
  have hCY : ⁅d.D₂, d.D₂⁆ ≤ d.Y := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact h.D₂_commutator_mem_Y hK hx hy
  refine le_antisymm hCY ?_
  set C : Subgroup G := ⁅d.D₂, d.D₂⁆ with hC
  have hFC : d.F ≤ C :=
    F_le_commutator_A₂.trans (Subgroup.commutator_mono h.A₂_le_D₂' h.A₂_le_D₂')
  have hWC : d.W ≤ C := by
    rw [← h.commutator_V₃_eq_W hK]
    exact Subgroup.commutator_mono (h.V₃_le_D₂ hK) (h.V₃_le_D₂ hK)
  have hθ'F : ∀ y ∈ d.Y, y⁻¹ * d.t * y * d.t ∈ d.F := fun y hy => by
    have := h.crossed_mem_F_of_mem_Y (inv_mem hy)
    rwa [inv_inv] at this
  have hcomm : ∀ y₁ ∈ d.Y, ∀ y₂ ∈ d.Y, (y₁⁻¹ * d.t * y₁ * d.t) * y₂ = y₂ * (y₁⁻¹ * d.t * y₁ * d.t) :=
    fun y₁ hy₁ y₂ hy₂ => h.Y_comm (h.F_le_Y (hθ'F y₁ hy₁)) hy₂
  let R₀ : Set SU52 := {φ | φ ∈ Fsub ∧ ∃ y ∈ C, y⁻¹ * d.t * y * d.t = d.ι φ}
  have h1 : (1 : SU52) ∈ R₀ := ⟨one_mem _, 1, one_mem _, by simp [h.t_mul_t]⟩
  have hmul : ∀ φ ∈ R₀, ∀ ψ ∈ R₀, φ * ψ ∈ R₀ := by
    rintro φ ⟨hφ, y₁, hy₁, e₁⟩ ψ ⟨hψ, y₂, hy₂, e₂⟩
    refine ⟨mul_mem hφ hψ, y₁ * y₂, mul_mem hy₁ hy₂, ?_⟩
    rw [crossed_mul h.t_mul_t (hcomm y₁ (hCY hy₁) y₂ (hCY hy₂)), e₁, e₂, map_mul]
  have hinvR : ∀ φ ∈ R₀, φ⁻¹ ∈ R₀ := by
    rintro φ ⟨hφ, y, hy, e⟩
    refine ⟨inv_mem hφ, y⁻¹, inv_mem hy, ?_⟩
    have hx : (y⁻¹ * d.t * y * d.t) * y = y * (y⁻¹ * d.t * y * d.t) :=
      (hcomm y (hCY hy) y (hCY hy))
    rw [crossed_inv h.t_mul_t hx, e, map_inv]
  let R : Subgroup SU52 :=
    { carrier := R₀
      one_mem' := h1
      mul_mem' := fun {a b} ha hb => hmul a ha b hb
      inv_mem' := fun {a} ha => hinvR a ha }
  have hRF : R ≤ Fsub := fun φ hφ => hφ.1
  have hRL : ∀ (A : Matrix (Fin 2) (Fin 2) F4) (hA : IsUnit A.det), ∀ r ∈ R,
      levSU A hA * r * (levSU A hA)⁻¹ ∈ R := by
    intro A hA φ hφ
    obtain ⟨hφF, y, hy, e⟩ := hφ
    have hl : d.ι (levSU A hA) ∈ d.Lev :=
      ⟨levSU A hA, ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA.ne_zero, rfl⟩, rfl⟩
    have hlN : d.ι (levSU A hA) ∈ normalizer (d.A₂ : Set G) := (h.Lev_le_NLA₂ hl).1
    have hlD₂ : d.ι (levSU A hA) ∈ normalizer (d.D₂ : Set G) :=
      h.XC₀_le_normalizer_D₂ (h.NHA₂_le_XC₀ (Subgroup.mem_inf.2 ⟨hlN, h.L_le_H (d.ι_mem _)⟩))
    have hlt : d.ι (levSU A hA) * d.t = d.t * d.ι (levSU A hA) :=
      h.t_comm_of_mem_L (d.ι_mem _)
    refine ⟨levSU_conj_mem_Fsub A hA hφF, d.ι (levSU A hA) * y * (d.ι (levSU A hA))⁻¹,
      conj_mem_commutator_of_mem_normalizer hlD₂ hy, ?_⟩
    rw [crossed_conj hlt, e]
    simp only [map_mul, map_inv]
  have hW4 : Nat.card d.W = 4 := h.sec4_9_W.1
  have hZ : Nat.card d.ZX₄ = 2 := by rw [Data.ZX₄, d.card_pull, card_ZX₄sub]
  obtain ⟨w, hw, hwZ⟩ : ∃ w ∈ d.W, w ∉ d.ZX₄ := by
    by_contra hcon
    have hle : d.W ≤ d.ZX₄ := fun w hw => by
      by_contra hn
      exact hcon ⟨w, hw, hn⟩
    have := Subgroup.card_le_of_le hle
    rw [hW4, hZ] at this
    omega
  have hzR : zSU ∈ R := ⟨(le_sup_right : ZX₄sub ≤ Fsub) zSU_mem, w, hWC hw, h.W_crossed_eq_z hw hwZ⟩
  have hRF' : R = Fsub := by
    rcases eq_bot_or_eq_Fsub_or_eq_A₂sub (hRF.trans Fsub_le_A₂sub) hRL with hb | hF | hA
    · exact absurd (mem_bot.1 (hb ▸ hzR)) zSU_ne_one
    · exact hF
    · exfalso
      have := Subgroup.card_le_of_le (hA ▸ hRF)
      rw [card_A₂sub, card_Fsub] at this
      norm_num at this
  intro y₀ hy₀
  obtain ⟨φ', hφ', e'⟩ := hθ'F y₀ hy₀
  have hφ'R : φ' ∈ R := hRF' ▸ hφ'
  obtain ⟨-, y, hy, e⟩ := hφ'R
  have hyY := hCY hy
  have hx : (y⁻¹ * d.t * y * d.t) * y = y * (y⁻¹ * d.t * y * d.t) := hcomm y hyY y hyY
  have hy1 : y⁻¹⁻¹ * d.t * y⁻¹ * d.t = (y⁻¹ * d.t * y * d.t)⁻¹ := crossed_inv h.t_mul_t hx
  have hc2 : ((y⁻¹)⁻¹ * d.t * y⁻¹ * d.t) * y₀ = y₀ * ((y⁻¹)⁻¹ * d.t * y⁻¹ * d.t) := by
    rw [hy1]
    have := hcomm y hyY y₀ hy₀
    exact (by
      have h3 := h.Y_comm (inv_mem (h.F_le_Y (hθ'F y hyY))) hy₀
      exact h3)
  have hprod := crossed_mul h.t_mul_t hc2
  rw [hy1, e, ← e'] at hprod
  rw [show (y⁻¹ * y₀) = y⁻¹ * y₀ from rfl] at hprod
  have hone : (y⁻¹ * y₀)⁻¹ * d.t * (y⁻¹ * y₀) * d.t = 1 := by
    rw [hprod]
    simp
  have hcommt : (y⁻¹ * y₀) * d.t = d.t * (y⁻¹ * y₀) := (crossed_eq_one_iff h.t_mul_t).1 hone
  have hFy : y⁻¹ * y₀ ∈ d.F := (h.mem_F_iff_Y _).2 ⟨mul_mem (inv_mem hyY) hy₀, hcommt⟩
  have := mul_mem hy (hFC hFy)
  rwa [mul_inv_cancel_left] at this

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
