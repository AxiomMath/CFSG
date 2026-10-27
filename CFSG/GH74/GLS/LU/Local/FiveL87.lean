module

public import CFSG.GH74.GLS.LU.Local.FiveCfg2
public import CFSG.GH74.GLS.LU.Local.FiveLeaves

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

section L87

variable (c : Cfg G p f z S K₁ K₂ t u H w₁ X₁ Y v)
include c

theorem Cfg.X3_le_R2 : X3 v X₁ ≤ RR t X₁ := c.X3_le_Y.trans c.Y_le_R2
theorem Cfg.X4_le_R2 : X4 v t X₁ ≤ RR t X₁ := c.X4_le_Y.trans c.Y_le_R2
theorem Cfg.X5_le_R2 : X5 v w₁ X₁ ≤ RR t X₁ := c.X5_le_Y'.trans c.Y'_le_R2
theorem Cfg.X6_le_R2 : X6 v t w₁ X₁ ≤ RR t X₁ := c.X6_le_Y'.trans c.Y'_le_R2

theorem Cfg.X4_comm_X6 (b86 : Five86 t w₁ X₁ v) :
    ∀ a ∈ X4 v t X₁, ∀ b ∈ X6 v t w₁ X₁, a * b = b * a := by
  intro a ha b hb
  have ha' : v⁻¹ * a * v ∈ XB t X₁ := mem_cjL.mp ha
  have hb' : v⁻¹ * b * v ∈ X6 v t w₁ X₁ := by
    have : b ∈ cjL v (X6 v t w₁ X₁) := by rw [b86.X6_v]; exact hb
    exact mem_cjL.mp this
  have hcomm := c.X2_central _ (c.X6_le_R2 hb') _ ha'
  calc a * b = v * ((v⁻¹ * a * v) * (v⁻¹ * b * v)) * v⁻¹ := by group
    _ = v * ((v⁻¹ * b * v) * (v⁻¹ * a * v)) * v⁻¹ := by rw [← hcomm]
    _ = b * a := by group

theorem Cfg.E_comm (b86 : Five86 t w₁ X₁ v) :
    ∀ x ∈ EE v t w₁ X₁, ∀ y ∈ EE v t w₁ X₁, x * y = y * x := by
  have h2 : ∀ a ∈ XB t X₁, ∀ a' ∈ XB t X₁, a * a' = a' * a := fun a ha a' ha' =>
    (c.X2_central a' (c.X2_le_R2 ha') a ha).symm
  have h4 : ∀ a ∈ X4 v t X₁, ∀ a' ∈ X4 v t X₁, a * a' = a' * a := fun a ha a' ha' =>
    c.b83.Y_ab.1 a (c.X4_le_Y ha) a' (c.X4_le_Y ha')
  have h6 : ∀ a ∈ X6 v t w₁ X₁, ∀ a' ∈ X6 v t w₁ X₁, a * a' = a' * a := fun a ha a' ha' =>
    c.b85.Yw_ab.1.1 a (c.X6_le_Y' ha) a' (c.X6_le_Y' ha')
  have h24 : ∀ a ∈ XB t X₁, ∀ b ∈ X4 v t X₁, a * b = b * a := fun a ha b hb =>
    (c.X2_central b (c.X4_le_R2 hb) a ha).symm
  have h26 : ∀ a ∈ XB t X₁, ∀ b ∈ X6 v t w₁ X₁, a * b = b * a := fun a ha b hb =>
    (c.X2_central b (c.X6_le_R2 hb) a ha).symm
  have h46 := c.X4_comm_X6 b86
  have h246 : ∀ x ∈ XB t X₁ ⊔ X4 v t X₁, ∀ b ∈ X6 v t w₁ X₁, x * b = b * x :=
    commute_sup_left h26 h46
  exact commute_sup (commute_sup h2 h4 h24) h6 h246

theorem Cfg.E_pow (b86 : Five86 t w₁ X₁ v) : ∀ x ∈ EE v t w₁ X₁, x ^ 5 = 1 := by
  have h24 : ∀ a ∈ XB t X₁, ∀ b ∈ X4 v t X₁, a * b = b * a := fun a ha b hb =>
    (c.X2_central b (c.X4_le_R2 hb) a ha).symm
  have h26 : ∀ a ∈ XB t X₁, ∀ b ∈ X6 v t w₁ X₁, a * b = b * a := fun a ha b hb =>
    (c.X2_central b (c.X6_le_R2 hb) a ha).symm
  have h46 := c.X4_comm_X6 b86
  have h246 : ∀ x ∈ XB t X₁ ⊔ X4 v t X₁, ∀ b ∈ X6 v t w₁ X₁, x * b = b * x :=
    commute_sup_left h26 h46
  exact sup_pow_eq_one h246
    (sup_pow_eq_one h24 (fun a ha => pow_five_of_card c.card_X2 ha)
      (fun a ha => pow_five_of_card c.card_X4 ha))
    (fun a ha => pow_five_of_card c.card_X6 ha)

theorem Cfg.A_card : Nat.card ↥(XB t X₁ ⊔ X4 v t X₁ : Subgroup G) = 25 := by
  have hd : XB t X₁ ⊓ X4 v t X₁ = ⊥ := by
    apply eq_bot_iff.mpr
    calc XB t X₁ ⊓ X4 v t X₁ ≤ XB t X₁ ⊓ Y := inf_le_inf_left _ c.X4_le_Y
      _ = ⊥ := c.X2_inf_Y
  rw [card_sup_of_commute_disjoint (fun a ha b hb =>
    (c.X2_central b (c.X4_le_R2 hb) a ha).symm) hd, c.card_X2, c.card_X4]

theorem Cfg.E_card (b86 : Five86 t w₁ X₁ v) : Nat.card ↥(EE v t w₁ X₁) = 5 ^ 3 := by
  have hd : (XB t X₁ ⊔ X4 v t X₁) ⊓ X6 v t w₁ X₁ = ⊥ := by
    apply eq_bot_iff.mpr
    calc (XB t X₁ ⊔ X4 v t X₁) ⊓ X6 v t w₁ X₁ ≤ (XB t X₁ ⊔ Y) ⊓ cjL w₁ Y :=
          inf_le_inf (sup_le_sup_left c.X4_le_Y _) c.X6_le_Y'
      _ = ⊥ := c.W_inf_Y'
  have hc : ∀ a ∈ XB t X₁ ⊔ X4 v t X₁, ∀ b ∈ X6 v t w₁ X₁, a * b = b * a :=
    fun a ha b hb => c.E_comm b86 a (Subgroup.mem_sup_left ha) b (Subgroup.mem_sup_right hb)
  rw [EE, card_sup_of_commute_disjoint hc hd, c.A_card, c.card_X6]
  norm_num

theorem Cfg.E_H : ∀ h ∈ H, cjL h (EE v t w₁ X₁) = EE v t w₁ X₁ :=
  (c.hinv_X2.sup c.hinv_X4).sup c.hinv_X6

theorem Cfg.cjL_v_E (b86 : Five86 t w₁ X₁ v) : cjL v (EE v t w₁ X₁) = EE v t w₁ X₁ := by
  have h4 : cjL v (X4 v t X₁) = XB t X₁ := by
    show cjL v (cjL v (XB t X₁)) = _
    rw [cjL_cjL]; exact c.hinv_X2 _ c.v_sq'
  rw [EE, cjL_sup, cjL_sup, b86.X6_v, h4]
  show X4 v t X₁ ⊔ XB t X₁ ⊔ X6 v t w₁ X₁ = _
  rw [sup_comm (X4 v t X₁)]

theorem Cfg.cjL_tv_D (b86 : Five86 t w₁ X₁ v) :
    cjL (t * v) (DD v w₁ X₁) = XB t X₁ ⊔ X4 v t X₁ ⊔ X5 v w₁ X₁ := by
  have h1 : cjL (t * v) X₁ = X4 v t X₁ := by rw [← cjL_cjL]; exact c.t_X3
  have h3 : cjL (t * v) (X3 v X₁) = XB t X₁ := by
    rw [← cjL_cjL]
    have : cjL v (X3 v X₁) = X₁ := by
      show cjL v (cjL v X₁) = X₁
      rw [cjL_cjL]; exact c.hinv_X1 _ c.v_sq'
    rw [this]
  rw [DD, cjL_sup, cjL_sup, h1, h3, b86.X5_tv, sup_comm (X4 v t X₁) (XB t X₁)]

theorem Cfg.D_card (b86 : Five86 t w₁ X₁ v) : Nat.card ↥(DD v w₁ X₁) = 5 ^ 3 := by
  rw [← card_cjL (t * v), c.cjL_tv_D b86]
  have hA : XB t X₁ ≤ XB t X₁ ⊔ X4 v t X₁ := le_sup_left
  have hAR : XB t X₁ ⊔ X4 v t X₁ ≤ RR t X₁ := sup_le c.X2_le_R2 c.X4_le_R2
  have hnorm : X5 v w₁ X₁ ≤ normalizer ((XB t X₁ ⊔ X4 v t X₁ : Subgroup G) : Set G) :=
    c.X5_le_R2.trans (c.R2_le_normalizer hA hAR)
  have h := card_sup_mul_card_inf' hnorm
  have hd : X5 v w₁ X₁ ⊓ (XB t X₁ ⊔ X4 v t X₁) = ⊥ := by
    apply eq_bot_iff.mpr
    calc X5 v w₁ X₁ ⊓ (XB t X₁ ⊔ X4 v t X₁) ≤ cjL w₁ Y ⊓ (XB t X₁ ⊔ Y) :=
          inf_le_inf c.X5_le_Y' (sup_le_sup_left c.X4_le_Y _)
      _ = ⊥ := by rw [inf_comm]; exact c.W_inf_Y'
  rw [hd, Subgroup.card_bot, mul_one, c.card_X5, c.A_card, sup_comm] at h
  rw [h]
  norm_num

theorem Cfg.E_le_R2 : EE v t w₁ X₁ ≤ RR t X₁ :=
  sup_le (sup_le c.X2_le_R2 c.X4_le_R2) c.X6_le_R2

theorem Cfg.X2_le_E : XB t X₁ ≤ EE v t w₁ X₁ := le_sup_left.trans le_sup_left
theorem Cfg.X4_le_E : X4 v t X₁ ≤ EE v t w₁ X₁ := le_sup_right.trans le_sup_left
theorem Cfg.X6_le_E : X6 v t w₁ X₁ ≤ EE v t w₁ X₁ := le_sup_right
theorem Cfg.X1_le_D : X₁ ≤ DD v w₁ X₁ := le_sup_left.trans le_sup_left
theorem Cfg.X3_le_D : X3 v X₁ ≤ DD v w₁ X₁ := le_sup_right.trans le_sup_left
theorem Cfg.X5_le_D : X5 v w₁ X₁ ≤ DD v w₁ X₁ := le_sup_right

theorem Cfg.ED_eq : EE v t w₁ X₁ ⊔ DD v w₁ X₁ = RR t X₁ ⊔ X₁ := by
  apply le_antisymm
  · refine sup_le (c.E_le_R2.trans le_sup_left) ?_
    exact sup_le (sup_le le_sup_right (c.X3_le_R2.trans le_sup_left))
      (c.X5_le_R2.trans le_sup_left)
  · refine sup_le ?_ (c.X1_le_D.trans le_sup_right)
    have hY : Y ≤ EE v t w₁ X₁ ⊔ DD v w₁ X₁ := by
      rw [c.Y_eq]
      exact sup_le (c.X3_le_D.trans le_sup_right) (c.X4_le_E.trans le_sup_left)
    have hY' : cjL w₁ Y ≤ EE v t w₁ X₁ ⊔ DD v w₁ X₁ := by
      rw [c.Y'_eq]
      exact sup_le (c.X5_le_D.trans le_sup_right) (c.X6_le_E.trans le_sup_left)
    rw [c.b85.R_eq]
    exact sup_le (sup_le (c.X2_le_E.trans le_sup_left) hY) hY'

theorem Cfg.ED_card : Nat.card ↥(RR t X₁ ⊔ X₁ : Subgroup G) = 5 ^ 6 := by
  have hnorm : X₁ ≤ normalizer ((RR t X₁ : Subgroup G) : Set G) :=
    (c.b82.X₁_syl.1).trans c.K1_le_normalizer_RR
  have hd : X₁ ⊓ RR t X₁ = ⊥ := by
    apply eq_bot_iff.mpr
    calc X₁ ⊓ RR t X₁ ≤ K₁ ⊓ RR t X₁ := inf_le_inf_right _ c.b82.X₁_syl.1
      _ = ⊥ := c.K1_inf_RR
  have h := card_sup_mul_card_inf' hnorm
  rw [hd, Subgroup.card_bot, mul_one, c.card_X1, c.b85.R_card, sup_comm] at h
  rw [h]
  norm_num

theorem Cfg.D_le_normalizer_E (b86 : Five86 t w₁ X₁ v) :
    DD v w₁ X₁ ≤ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) := by
  have hR := c.R2_le_normalizer (A := EE v t w₁ X₁) c.X2_le_E c.E_le_R2
  have h3 : X3 v X₁ ≤ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) := c.X3_le_R2.trans hR
  have h5 : X5 v w₁ X₁ ≤ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) := c.X5_le_R2.trans hR
  have h1 : X₁ ≤ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) := by
    intro x hx
    have hx' : v * x * v⁻¹ ∈ X3 v X₁ := mem_cjL_self hx
    have hxe : cjL (v * x * v⁻¹) (EE v t w₁ X₁) = EE v t w₁ X₁ :=
      cjL_eq_of_mem_normalizer (h3 hx')
    have hvE := c.cjL_v_E b86
    have hvE' : cjL v⁻¹ (EE v t w₁ X₁) = EE v t w₁ X₁ := by
      conv_lhs => rw [← hvE]
      rw [cjL_cjL, inv_mul_cancel, cjL_one]
    apply mem_normalizer_of_cjL_eq
    have e : x = v⁻¹ * (v * x * v⁻¹) * v := by group
    calc cjL x (EE v t w₁ X₁) = cjL (v⁻¹ * (v * x * v⁻¹) * v) (EE v t w₁ X₁) := by rw [← e]
      _ = cjL v⁻¹ (cjL (v * x * v⁻¹) (cjL v (EE v t w₁ X₁))) := by
          rw [cjL_cjL, cjL_cjL]
      _ = EE v t w₁ X₁ := by rw [hvE, hxe, hvE']
  exact sup_le (sup_le h1 h3) h5

theorem Cfg.ED_disj (b86 : Five86 t w₁ X₁ v) : EE v t w₁ X₁ ⊓ DD v w₁ X₁ = ⊥ := by
  have h := card_sup_mul_card_inf' (c.D_le_normalizer_E b86)
  have hsup : DD v w₁ X₁ ⊔ EE v t w₁ X₁ = RR t X₁ ⊔ X₁ := by rw [sup_comm]; exact c.ED_eq
  rw [hsup, c.ED_card, c.D_card b86, c.E_card b86] at h
  have h1 : Nat.card ↥(DD v w₁ X₁ ⊓ EE v t w₁ X₁ : Subgroup G) = 1 := by
    have h6 : (5 : ℕ) ^ 6 = 15625 := by norm_num
    have h3 : (5 : ℕ) ^ 3 = 125 := by norm_num
    rw [h6, h3] at h
    omega
  rw [inf_comm]
  exact Subgroup.eq_bot_of_card_eq _ h1

end L87

theorem leaf87 : Leaf87 := by
  intro G _ _ p f z S K₁ K₂ t u ctx H w₁ b66 X₁ b82 Y b83 v b84 b85 b86
  have c : Cfg G p f z S K₁ K₂ t u H w₁ X₁ Y v := ⟨⟨⟨⟨ctx, b66, b82⟩, b83⟩, b84⟩, b85⟩
  exact ⟨⟨c.E_comm b86, c.E_pow b86⟩, c.E_card b86, c.E_H, c.D_card b86, c.ED_disj b86, c.ED_eq,
    by rw [c.ED_eq]; exact c.ED_card⟩


end CFSG.GH74.GLS.LU.Local.Five
