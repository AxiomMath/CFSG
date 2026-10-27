module

public import CFSG.GH74.GLS.LU.Local.FiveL87
public import CFSG.GH74.GLS.LU.Local.FiveL85b

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

structure Cfg8 (G : Type) [Group G] [Finite G] (p f : ℕ) (z : G) (S : Sylow 2 G)
    (K₁ K₂ : Subgroup G) (t u : G) (H : Subgroup G) (w₁ : G) (X₁ Y : Subgroup G) (v : G) : Prop
    extends Cfg G p f z S K₁ K₂ t u H w₁ X₁ Y v where
  b86 : Five86 t w₁ X₁ v
  b87 : Five87 t H w₁ X₁ v

section L88a

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ H : Subgroup G}
  {t u w₁ v : G} {X₁ Y : Subgroup G}

theorem Cfg8.w₁_N (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    w₁ ∈ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) := by
  apply mem_normalizer_of_cjL_eq
  have h2 : cjL w₁ (XB t X₁) = XB t X₁ := cjL_eq_of_comm (fun a ha => c.w₁_comm_X2 a ha)
  have h4 : cjL w₁ (X4 v t X₁) = X6 v t w₁ X₁ := rfl
  have h6 : cjL w₁ (X6 v t w₁ X₁) = X4 v t X₁ := by
    show cjL w₁ (cjL w₁ (X4 v t X₁)) = X4 v t X₁
    rw [cjL_cjL]
    have hww : w₁ * w₁ = z := by rw [← pow_two]; exact c.b66.w₁_sq
    rw [hww]
    apply cjL_eq_of_mem_normalizer
    apply CFSG.Walter.J1.mem_normalizer_of_conj_mem
    intro y hy
    have hyY : y ∈ Y := c.X4_le_Y hy
    rw [c.z_inv_Y y hyY]
    exact inv_mem hy
  rw [EE, cjL_sup, cjL_sup, h2, h4, h6]
  rw [sup_right_comm]

theorem Cfg8.v_N (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    v ∈ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) :=
  mem_normalizer_of_cjL_eq (c.cjL_v_E c.b86)

theorem Cfg8.D_le_N (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    DD v w₁ X₁ ≤ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) := c.D_le_normalizer_E c.b86

theorem Cfg8.X1_N (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    X₁ ≤ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) :=
  c.X1_le_D.trans c.D_le_N

theorem Cfg8.K1_N (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    K₁ ≤ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) := by
  rw [← c.b82.K₁_gen, Subgroup.closure_le]
  intro x hx
  rcases hx with hx | hx
  · exact c.X1_N hx
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]; exact c.w₁_N

theorem Cfg8.H_N (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    H ≤ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) := fun h hh =>
  mem_normalizer_of_cjL_eq (c.E_H h hh)

theorem Cfg8.RR_N (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    RR t X₁ ≤ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) :=
  c.R2_le_normalizer c.X2_le_E c.E_le_R2

theorem Cfg8.P_N (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    w₁ * v ∈ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) := mul_mem c.w₁_N c.v_N

theorem Cfg8.NG_X2_le_N (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    normalizer ((XB t X₁ : Subgroup G) : Set G) ≤ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) := by
  rw [c.N_X2_eq]
  exact sup_le (sup_le c.RR_N c.K1_N) c.H_N

theorem Cfg8.L_P_le_N (c : Cfg8 G p f z S K₁ K₂ t u H w₁ X₁ Y v) :
    cjL (w₁ * v) K₁ ≤ normalizer ((EE v t w₁ X₁ : Subgroup G) : Set G) := by
  rintro _ ⟨k, hk, rfl⟩
  have hk' : (MulAut.conj (w₁ * v)).toMonoidHom k = (w₁ * v) * k * (w₁ * v)⁻¹ := by
    simp [MulAut.conj_apply, mul_assoc]
  rw [hk']
  exact mul_mem (mul_mem c.P_N (c.K1_N hk)) (inv_mem c.P_N)

end L88a

end CFSG.GH74.GLS.LU.Local.Five
