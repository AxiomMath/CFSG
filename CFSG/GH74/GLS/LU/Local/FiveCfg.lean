module

public import CFSG.GH74.GLS.LU.Local.FiveFacts

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

structure Cfg2 (G : Type) [Group G] [Finite G] (p f : ℕ) (z : G) (S : Sylow 2 G)
    (K₁ K₂ : Subgroup G) (t u : G) (H : Subgroup G) (w₁ : G) (X₁ : Subgroup G) : Prop where
  ctx : FiveCtx G p f z S K₁ K₂ t u
  b66 : Five66 z t u K₁ K₂ H w₁
  b82 : Five82 z t u K₁ K₂ H w₁ X₁

structure Cfg3 (G : Type) [Group G] [Finite G] (p f : ℕ) (z : G) (S : Sylow 2 G)
    (K₁ K₂ : Subgroup G) (t u : G) (H : Subgroup G) (w₁ : G) (X₁ Y : Subgroup G) : Prop
    extends Cfg2 G p f z S K₁ K₂ t u H w₁ X₁ where
  b83 : Five83 z t u H X₁ Y

structure Cfg4 (G : Type) [Group G] [Finite G] (p f : ℕ) (z : G) (S : Sylow 2 G)
    (K₁ K₂ : Subgroup G) (t u : G) (H : Subgroup G) (w₁ : G) (X₁ Y : Subgroup G) (v : G) : Prop
    extends Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y where
  b84 : Five84 z t u H X₁ Y v

structure Cfg (G : Type) [Group G] [Finite G] (p f : ℕ) (z : G) (S : Sylow 2 G)
    (K₁ K₂ : Subgroup G) (t u : G) (H : Subgroup G) (w₁ : G) (X₁ Y : Subgroup G) (v : G) : Prop
    extends Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v where
  b85 : Five85 z t u K₁ K₂ H w₁ X₁ Y v

section Cfg

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg2.hc (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : LUComps G (p ^ f) z K₁ K₂ := c.ctx.hyp.1

theorem Cfg2.hs (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : LUSyl G z S K₁ K₂ t u := c.ctx.hyp.2.1

theorem Cfg2.t_sq (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : t * t = 1 := c.hs.t_sq

theorem Cfg2.w₁_NN (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : w₁ ∈ NN z u := by
  have hz : w₁ * z * w₁⁻¹ = z := by
    have := c.hc.cz₁ c.b66.w₁_mem
    calc w₁ * z * w₁⁻¹ = (z * w₁) * w₁⁻¹ := by rw [this]
      _ = z := by group
  have hu : w₁ * u * w₁⁻¹ = u * z := c.b66.w₁_u
  apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
  intro x hx
  have hle : UU z u ≤ (UU z u).comap (MulAut.conj w₁).toMonoidHom := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_comap]
      show w₁ * z * w₁⁻¹ ∈ _
      rw [hz]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
    · rw [Subgroup.mem_comap]
      show w₁ * u * w₁⁻¹ ∈ _
      rw [hu]
      exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  have := hle hx
  rw [Subgroup.mem_comap] at this
  exact this

theorem Cfg2.cjL_H (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) {n : G} (hn : n ∈ NN z u) :
    cjL n H = H := c.b66.N_normH n hn

theorem Cfg2.hinv_X1 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : HInv H X₁ := c.b82.H_normX₁
theorem Cfg2.hinv_X2 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : HInv H (XB t X₁) :=
  c.hinv_X1.conj c.b66.t_normH
theorem Cfg4.hinv_X3 (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : HInv H (X3 v X₁) :=
  c.hinv_X1.conj (c.cjL_H c.b84.v_N)
theorem Cfg4.hinv_X4 (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : HInv H (X4 v t X₁) :=
  c.hinv_X2.conj (c.cjL_H c.b84.v_N)
theorem Cfg4.hinv_X5 (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : HInv H (X5 v w₁ X₁) :=
  c.hinv_X3.conj (c.cjL_H c.w₁_NN)
theorem Cfg4.hinv_X6 (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : HInv H (X6 v t w₁ X₁) :=
  c.hinv_X4.conj (c.cjL_H c.w₁_NN)
theorem Cfg2.hinv_XX (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : HInv H (XX t X₁) :=
  c.hinv_X1.sup c.hinv_X2
theorem Cfg3.hinv_Y (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : HInv H Y := c.b83.Y_H

theorem Cfg2.card_X1 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : Nat.card ↥X₁ = 5 := c.b82.X₁_card
theorem Cfg2.card_X2 (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) : Nat.card ↥(XB t X₁) = 5 :=
  (card_cjL t X₁).trans c.card_X1
theorem Cfg4.card_X3 (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : Nat.card ↥(X3 v X₁) = 5 :=
  (card_cjL v X₁).trans c.card_X1
theorem Cfg4.card_X4 (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : Nat.card ↥(X4 v t X₁) = 5 :=
  (card_cjL v _).trans c.card_X2
theorem Cfg4.card_X5 (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : Nat.card ↥(X5 v w₁ X₁) = 5 :=
  (card_cjL w₁ _).trans c.card_X3
theorem Cfg4.card_X6 (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : Nat.card ↥(X6 v t w₁ X₁) = 5 :=
  (card_cjL w₁ _).trans c.card_X4

theorem Cfg3.XX_comm (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    ∀ a ∈ XX t X₁, ∀ b ∈ Y, a * b = b * a :=
  fun a ha b hb => c.b83.XY_ab.1 a (Subgroup.mem_sup_left ha) b (Subgroup.mem_sup_right hb)

theorem Cfg3.XX_card (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : Nat.card ↥(XX t X₁) = 25 := by
  have h := card_sup_mul_card_inf' (le_normalizer_of_commute c.XX_comm)
  rw [c.b83.XY_card, c.b83.XY_disj, Subgroup.card_bot, c.b83.Y_card] at h
  omega

theorem Cfg3.X1_comm_X2 (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) :
    ∀ a ∈ X₁, ∀ b ∈ XB t X₁, a * b = b * a := fun a ha b hb =>
  c.b83.XY_ab.1 a (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha)) b
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))

theorem Cfg3.X1_inf_X2 (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : X₁ ⊓ XB t X₁ = ⊥ := by
  have h := card_sup_mul_card_inf' (le_normalizer_of_commute c.X1_comm_X2)
  have h25 : Nat.card ↥(X₁ ⊔ XB t X₁ : Subgroup G) = 25 := c.XX_card
  rw [h25, c.card_X1, c.card_X2] at h
  have : Nat.card ↥(X₁ ⊓ XB t X₁ : Subgroup G) = 1 := by omega
  exact Subgroup.eq_bot_of_card_eq _ this

theorem RR_le_normalizer (t : G) (X₁ : Subgroup G) :
    RR t X₁ ≤ normalizer ((XB t X₁ : Subgroup G) : Set G) :=
  CFSG.LieType.BorelTits.pCoreOf_le 5 _

theorem RR_pGroup (t : G) (X₁ : Subgroup G) : IsPGroup 5 ↥(RR t X₁) :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  CFSG.LieType.BorelTits.pCoreOf_isPGroup 5 _

theorem normalizer_le_normalizer_RR (t : G) (X₁ : Subgroup G) :
    normalizer ((XB t X₁ : Subgroup G) : Set G) ≤ normalizer ((RR t X₁ : Subgroup G) : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 5 _

theorem Cfg.X2_le_R2 (c : Cfg G p f z S K₁ K₂ t u H w₁ X₁ Y v) : XB t X₁ ≤ RR t X₁ := by
  rw [c.b85.R_eq]; exact le_sup_left.trans le_sup_left

theorem Cfg.Y_le_R2 (c : Cfg G p f z S K₁ K₂ t u H w₁ X₁ Y v) : Y ≤ RR t X₁ := by
  rw [c.b85.R_eq]; exact le_sup_right.trans le_sup_left

theorem Cfg.Y'_le_R2 (c : Cfg G p f z S K₁ K₂ t u H w₁ X₁ Y v) : cjL w₁ Y ≤ RR t X₁ := by
  rw [c.b85.R_eq]; exact le_sup_right

theorem Cfg2.X2_central (c : Cfg2 G p f z S K₁ K₂ t u H w₁ X₁) :
    ∀ r ∈ RR t X₁, ∀ x ∈ XB t X₁, r * x = x * r :=
  centralizes_of_five_group (RR_pGroup t X₁) c.card_X2 (RR_le_normalizer t X₁)

theorem Cfg.R2_le_normalizer (c : Cfg G p f z S K₁ K₂ t u H w₁ X₁ Y v) {A : Subgroup G}
    (hA : XB t X₁ ≤ A) (hAR : A ≤ RR t X₁) : RR t X₁ ≤ normalizer (A : Set G) := by
  intro r hr
  apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
  intro a ha
  have h1 : r * a * r⁻¹ * a⁻¹ ∈ A := hA (c.b85.R_cl2 r hr a (hAR ha))
  have : r * a * r⁻¹ = (r * a * r⁻¹ * a⁻¹) * a := by group
  rw [this]
  exact mul_mem h1 ha

theorem Cfg4.X3_le_Y (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : X3 v X₁ ≤ Y := by
  have : cjL v X₁ ≤ cjL v (XX t X₁) := cjL_mono v le_sup_left
  rwa [c.b84.v_X] at this

theorem Cfg4.X4_le_Y (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : X4 v t X₁ ≤ Y := by
  have : cjL v (XB t X₁) ≤ cjL v (XX t X₁) := cjL_mono v le_sup_right
  rwa [c.b84.v_X] at this

theorem Cfg4.Y_eq (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : Y = X3 v X₁ ⊔ X4 v t X₁ := by
  have h := c.b84.v_X
  rw [XX, cjL_sup] at h
  exact h.symm

theorem Cfg4.X5_le_Y' (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : X5 v w₁ X₁ ≤ cjL w₁ Y :=
  cjL_mono w₁ c.X3_le_Y

theorem Cfg4.X6_le_Y' (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) : X6 v t w₁ X₁ ≤ cjL w₁ Y :=
  cjL_mono w₁ c.X4_le_Y

theorem Cfg4.Y'_eq (c : Cfg4 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    cjL w₁ Y = X5 v w₁ X₁ ⊔ X6 v t w₁ X₁ := by
  rw [c.Y_eq, cjL_sup]

theorem Cfg3.Y_card (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : Nat.card ↥Y = 25 := c.b83.Y_card
theorem Cfg3.Y'_card (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : Nat.card ↥(cjL w₁ Y) = 25 :=
  (card_cjL w₁ Y).trans c.b83.Y_card

theorem Cfg3.X2_inf_Y (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : XB t X₁ ⊓ Y = ⊥ := by
  apply eq_bot_iff.mpr
  calc XB t X₁ ⊓ Y ≤ XX t X₁ ⊓ Y := inf_le_inf_right _ le_sup_right
    _ = ⊥ := c.b83.XY_disj

theorem Cfg3.W_card (c : Cfg3 G p f z S K₁ K₂ t u H w₁ X₁ Y) : Nat.card ↥(XB t X₁ ⊔ Y : Subgroup G) = 125 := by
  have h := card_sup_of_commute_disjoint (A := XB t X₁) (B := Y)
    (fun a ha b hb => c.XX_comm a (Subgroup.mem_sup_right ha) b hb) c.X2_inf_Y
  rw [h, c.card_X2, c.Y_card]

theorem Cfg.W_inf_Y' (c : Cfg G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    (XB t X₁ ⊔ Y) ⊓ cjL w₁ Y = ⊥ := by
  have hWR : XB t X₁ ⊔ Y ≤ RR t X₁ := sup_le c.X2_le_R2 c.Y_le_R2
  have hY'N : cjL w₁ Y ≤ normalizer ((XB t X₁ ⊔ Y : Subgroup G) : Set G) :=
    (cjL_mono w₁ le_rfl : cjL w₁ Y ≤ cjL w₁ Y).trans
      (c.Y'_le_R2.trans (c.R2_le_normalizer le_sup_left hWR))
  have h := card_sup_mul_card_inf' hY'N
  have hsup : cjL w₁ Y ⊔ (XB t X₁ ⊔ Y) = RR t X₁ := by
    rw [sup_comm]; exact c.b85.R_eq.symm
  rw [hsup, c.b85.R_card, c.Y'_card, c.W_card, inf_comm] at h
  have h1 : Nat.card ↥((XB t X₁ ⊔ Y) ⊓ cjL w₁ Y : Subgroup G) = 1 := by
    have : (5 : ℕ) ^ 5 = 3125 := by norm_num
    omega
  exact Subgroup.eq_bot_of_card_eq _ h1

end Cfg
end CFSG.GH74.GLS.LU.Local.Five
