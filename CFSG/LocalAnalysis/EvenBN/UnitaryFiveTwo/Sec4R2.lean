module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4D1

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped Pointwise

theorem card_sup_mul_card_inf_of_le_normalizer {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) (hK : K ≤ normalizer (H : Set G)) :
    Nat.card (H ⊔ K : Subgroup G) * Nat.card (H ⊓ K : Subgroup G) =
      Nat.card H * Nat.card K := by
  have := normal_subgroupOf_of_le_normalizer hK
  have := normal_subgroupOf_sup_of_le_normalizer hK
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient K H hK
  have h1 := card_eq_card_quotient_mul_card_subgroup (H.subgroupOf K)
  have h2 := card_eq_card_quotient_mul_card_subgroup (H.subgroupOf (K ⊔ H))
  have h3 : Nat.card (H.subgroupOf K) = Nat.card (H ⊓ K : Subgroup G) := by
    rw [← inf_subgroupOf_right]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
  have h4 : Nat.card (H.subgroupOf (K ⊔ H)) = Nat.card H :=
    Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv
  have h5 : Nat.card (↥K ⧸ H.subgroupOf K) = Nat.card (↥(K ⊔ H) ⧸ H.subgroupOf (K ⊔ H)) :=
    Nat.card_congr e.toEquiv
  rw [sup_comm, h2, h4, ← h5, h1, h3]
  ring

@[expose] def Data.R₂ {G : Type} [Group G] (d : Data G) : Subgroup G := d.R ⊔ d.V₂

@[expose] def Data.R₃ {G : Type} [Group G] (d : Data G) : Subgroup G :=
  oTwo (normalizer (d.R₂ : Set G))

@[expose] def Data.D₃ {G : Type} [Group G] (d : Data G) : Subgroup G :=
  normalizer (d.R₂ : Set G) ⊓ d.D₁

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem R_le_H (h : d.Hyp) : d.R ≤ d.H :=
  sup_le (fun _ hs => h.L_le_H (d.pull_le_L _ hs)) (zpowers_le.2 h.t_mem_H)

theorem card_R
    (h : d.Hyp) : Nat.card d.R = 2 ^ 11 := by
  have e := h.card_sup_kernel (X := d.S) (d.pull_le_L _)
  rw [h.centralizer_inf_H_eq, h.card_zpowers_t, d.card_S] at e
  exact e

theorem W_le_normalizer_R
    (h : d.Hyp) :
    d.W ≤ normalizer (d.R : Set G) := fun w hw => by
  refine mem_normalizer_fintype fun y hy => ?_
  have hle : d.R ≤ d.R.comap (MulAut.conj w).toMonoidHom := by
    refine sup_le (fun s hs => ?_) ?_
    · change w * s * w⁻¹ ∈ d.R
      rw [← mem_centralizer_iff.1 (d.W_le_centralizer hw) s hs, mul_inv_cancel_right]
      exact mem_sup_left hs
    · rw [zpowers_le]
      change w * d.t * w⁻¹ ∈ d.R
      have hc := h.W_crossed_mem_ZX₄ (inv_mem hw)
      rw [inv_inv] at hc
      rw [show w * d.t * w⁻¹ = (w * d.t * w⁻¹ * d.t) * d.t by
        rw [mul_assoc _ d.t d.t, h.t_mul_t, mul_one]]
      exact mul_mem (mem_sup_left (d.pull_mono (ZX₄sub_le_X₄sub.trans
        (le_sup_right : X₄sub ≤ Ssub)) hc)) (mem_sup_right (mem_zpowers _))
  exact hle hy

theorem R_inf_W
    (h : d.Hyp) :
    d.R ⊓ d.W = d.ZX₄ := by
  refine le_antisymm (fun x hx => ?_) (le_inf (fun z hz => mem_sup_left
    (d.pull_mono (ZX₄sub_le_X₄sub.trans (le_sup_right : X₄sub ≤ Ssub)) hz)) h.ZX₄_le_W)
  rw [← h.W_inf_H]
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2, h.R_le_H (Subgroup.mem_inf.1 hx).1⟩

theorem card_RW
    (h : d.Hyp) :
    Nat.card (d.R ⊔ d.W : Subgroup G) = 2 ^ 12 := by
  have e := card_sup_mul_card_inf_of_le_normalizer d.R d.W h.W_le_normalizer_R
  rw [h.R_inf_W, h.card_R, h.sec4_9_W.1, Data.ZX₄, d.card_pull, card_ZX₄sub] at e
  omega

theorem R_inf_V₂
    (h : d.Hyp) :
    d.R ⊓ d.V₂ = d.Z₂ := by
  refine le_antisymm (fun x hx => ?_) (le_inf (fun g hg => mem_sup_left
    (d.A₁_le_S (Z₂_le_A₁ hg))) h.Z₂_le_V₂)
  rw [← h.V₂_inf_H]
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2, h.R_le_H (Subgroup.mem_inf.1 hx).1⟩

theorem R_le_normalizer_Y
    (h : d.Hyp) :
    d.R ≤ normalizer (d.Y : Set G) := by
  refine sup_le h.S_le_normalizer_Y (zpowers_le.2 (mem_normalizer_fintype fun y hy => ?_))
  rw [h.t_inv]
  exact h.t_conj_mem_Y hy

theorem R_inf_Y
    (h : d.Hyp) :
    d.R ⊓ d.Y = d.F := by
  refine le_antisymm (fun x hx => ?_) (le_inf (fun f hf => mem_sup_left
    (d.A₂_le_S (d.F_le_A₂ hf))) h.F_le_Y)
  exact (h.mem_F_iff_Y x).2 ⟨(Subgroup.mem_inf.1 hx).2,
    mem_centralizer_singleton_iff.1 (h.R_le_H (Subgroup.mem_inf.1 hx).1)⟩

theorem card_RY
    (h : d.Hyp) :
    Nat.card (d.R ⊔ d.Y : Subgroup G) = 2 ^ 15 := by
  have e := card_sup_mul_card_inf_of_le_normalizer d.Y d.R h.R_le_normalizer_Y
  rw [inf_comm, h.R_inf_Y, sup_comm, d.card_F, h.card_R, h.sec4_6.2.2.2.2.1] at e
  omega

theorem R₂_eq_sup
    (h : d.Hyp) :
    d.R₂ = (d.R ⊔ d.W) ⊔ d.V₂ := by
  rw [Data.R₂, sup_assoc, sup_eq_right.2 h.W_le_V₂]

theorem RW_inf_V₂
    (h : d.Hyp) :
    (d.R ⊔ d.W) ⊓ d.V₂ = d.Z₂ ⊔ d.W := by
  refine le_antisymm (fun x hx => ?_) (le_inf (sup_le_sup_right (fun g hg => mem_sup_left
    (d.A₁_le_S (Z₂_le_A₁ hg))) _) (sup_le h.Z₂_le_V₂ h.W_le_V₂))
  obtain ⟨hxRW, hxV⟩ := Subgroup.mem_inf.1 hx
  have hset := coe_mul_of_right_le_normalizer_left d.R d.W h.W_le_normalizer_R
  obtain ⟨r, hr, w, hw, rfl⟩ : x ∈ (d.R : Set G) * (d.W : Set G) := by
    rw [← hset]
    exact hxRW
  have hrV : r ∈ d.V₂ := by
    have := mul_mem hxV (inv_mem (h.W_le_V₂ hw))
    rwa [mul_inv_cancel_right] at this
  have hrZ : r ∈ d.Z₂ := by
    rw [← h.R_inf_V₂]
    exact Subgroup.mem_inf.2 ⟨hr, hrV⟩
  exact mul_mem (mem_sup_left hrZ) (mem_sup_right hw)

theorem card_Z₂_sup_W
    (h : d.Hyp) :
    Nat.card (d.Z₂ ⊔ d.W : Subgroup G) = 2 ^ 4 := by
  have hinf : d.Z₂ ⊓ d.W = d.ZX₄ := by
    refine le_antisymm (fun x hx => ?_) (le_inf (by rw [Z₂_eq_sup]; exact le_sup_right)
      h.ZX₄_le_W)
    rw [← h.W_inf_H]
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2,
      h.L_le_H (d.pull_le_L _ (Subgroup.mem_inf.1 hx).1)⟩
  have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute d.Z₂ d.W
    fun g hg w hw => h.Y_comm (h.F_le_Y (Z₂_le_F hg)) (d.W_le_Y hw)).1
  rw [hinf, card_Z₂, h.sec4_9_W.1, Data.ZX₄, d.card_pull, card_ZX₄sub] at hc
  omega

end Data.Hyp

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem V₂_le_normalizer_RW
    (h : d.Hyp) :
    d.V₂ ≤ normalizer ((d.R ⊔ d.W : Subgroup G) : Set G) := fun v hv => by
  obtain ⟨hvY, hvW⟩ := (h.mem_V₂_iff).1 hv
  refine mem_normalizer_fintype fun y hy => ?_
  have hle : d.R ⊔ d.W ≤ (d.R ⊔ d.W).comap (MulAut.conj v).toMonoidHom := by
    refine sup_le (sup_le (fun s hs => ?_) ?_) fun w hw => ?_
    · change v * s * v⁻¹ ∈ d.R ⊔ d.W
      have hc := inv_mem (hvW s hs)
      rw [show (s * v * s⁻¹ * v⁻¹)⁻¹ = v * s * v⁻¹ * s⁻¹ by group] at hc
      rw [show v * s * v⁻¹ = (v * s * v⁻¹ * s⁻¹) * s by group]
      exact mul_mem (mem_sup_right hc) (mem_sup_left (mem_sup_left hs))
    · rw [zpowers_le]
      change v * d.t * v⁻¹ ∈ d.R ⊔ d.W
      have hz := h.crossed_mem_Z₂_of_mem_V₂ hv
      rw [show v * d.t * v⁻¹ = (v⁻¹ * d.t * v * d.t) * d.t by
        rw [inv_eq_of_mul_eq_one_right (h.Y_sq hvY), mul_assoc _ d.t d.t, h.t_mul_t, mul_one]]
      exact mem_sup_left (mul_mem (mem_sup_left (d.A₁_le_S (Z₂_le_A₁ hz)))
        (mem_sup_right (mem_zpowers _)))
    · change v * w * v⁻¹ ∈ d.R ⊔ d.W
      rw [h.Y_comm hvY (d.W_le_Y hw), mul_inv_cancel_right]
      exact mem_sup_right hw
  exact hle hy

theorem card_R₂
    (h : d.Hyp) :
    Nat.card d.R₂ = 2 ^ 14 := by
  have e := card_sup_mul_card_inf_of_le_normalizer (d.R ⊔ d.W) d.V₂ h.V₂_le_normalizer_RW
  rw [h.RW_inf_V₂, h.card_Z₂_sup_W, h.card_RW, h.card_V₂, ← h.R₂_eq_sup] at e
  omega

theorem R₂_inf_H
    (h : d.Hyp) :
    d.R₂ ⊓ d.H = d.R := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left h.R_le_H)
  obtain ⟨hxR, hxH⟩ := Subgroup.mem_inf.1 hx
  rw [h.R₂_eq_sup] at hxR
  have hset := coe_mul_of_right_le_normalizer_left (d.R ⊔ d.W) d.V₂ h.V₂_le_normalizer_RW
  obtain ⟨k, hk, v, hv, rfl⟩ : x ∈ ((d.R ⊔ d.W : Subgroup G) : Set G) * (d.V₂ : Set G) := by
    rw [← hset]
    exact hxR
  have hsetR := coe_mul_of_right_le_normalizer_left d.R d.W h.W_le_normalizer_R
  obtain ⟨r, hr, w, hw, rfl⟩ : k ∈ (d.R : Set G) * (d.W : Set G) := by
    rw [← hsetR]
    exact hk
  beta_reduce at hxH ⊢
  have hwvH : w * v ∈ d.H := by
    have := mul_mem (inv_mem (h.R_le_H hr)) hxH
    rwa [show r⁻¹ * (r * w * v) = w * v by group] at this
  have hwvZ : w * v ∈ d.Z₂ := by
    rw [← h.V₂_inf_H]
    exact Subgroup.mem_inf.2 ⟨mul_mem (h.W_le_V₂ hw) hv, hwvH⟩
  rw [mul_assoc]
  exact mul_mem hr (mem_sup_left (d.A₁_le_S (Z₂_le_A₁ hwvZ)))

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
