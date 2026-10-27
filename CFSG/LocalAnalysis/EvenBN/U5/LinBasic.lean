module

public import CFSG.LocalAnalysis.EvenBN.U5.LinParts
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofThirteenA

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

namespace CaseBData

variable (hl : d.LinCtx) (k : d.Know12) (c : d.CaseBData)
include hl k c

theorem lin_L₁_eq : d.L₁ = d.D ⊔ d.M₁ := k.s9_3.1

theorem lin_M₁_le_L₁ : d.M₁ ≤ d.L₁ := (lin_L₁_eq hl k c) ▸ le_sup_right

theorem lin_X_le_L₁ : c.X ≤ d.L₁ := c.X_le_M₁.trans (lin_M₁_le_L₁ hl k c)

theorem lin_Y_le_L₁ : c.Y ≤ d.L₁ := c.Y_le_M₁.trans (lin_M₁_le_L₁ hl k c)

theorem lin_X_le_Kc : c.X ≤ c.Kc := by
  unfold CaseBData.Kc
  rw [d.Kc_eq_normalClosureIn]
  exact le_normalClosureIn (lin_X_le_L₁ hl k c)

theorem lin_Kc_le_L₁ : c.Kc ≤ d.L₁ := by
  unfold CaseBData.Kc
  rw [d.Kc_eq_normalClosureIn]
  exact normalClosureIn_le_self _ _

theorem lin_L₁_le_normalizer_Kc : d.L₁ ≤ normalizer (c.Kc : Set G) := by
  unfold CaseBData.Kc
  rw [d.Kc_eq_normalClosureIn]
  exact le_normalizer_normalClosureIn _ _

theorem lin_map_conj_t_L₁ : d.L₁.map (MulAut.conj d.t).toMonoidHom = d.L₁ :=
  map_conj_eq_of_mem_normalizer hl.hyp.t_mem_normalizer_L₁

theorem lin_map_conj_t_X : c.X.map (MulAut.conj d.t).toMonoidHom = c.Y :=
  s313a_map_conj_t_X hl.toCaseHyp k c.S_syl c.P_le_S c.ψ c.card_k

theorem lin_Y_le_Kt : c.Y ≤ c.Kt := by
  rw [← lin_map_conj_t_X hl k c]
  exact map_mono (lin_X_le_Kc hl k c)

theorem lin_Kt_le_L₁ : c.Kt ≤ d.L₁ := by
  rw [← lin_map_conj_t_L₁ hl k c]
  exact map_mono (lin_Kc_le_L₁ hl k c)

theorem lin_L₁_le_normalizer_Kt : d.L₁ ≤ normalizer (c.Kt : Set G) := by
  intro g hg
  have hg' : d.t⁻¹ * g * d.t ∈ d.L₁ := by
    have := (mem_normalizer_iff.1 (inv_mem hl.hyp.t_mem_normalizer_L₁) g).1 hg
    rwa [inv_inv] at this
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨(d.t⁻¹ * g * d.t) * y * (d.t⁻¹ * g * d.t)⁻¹,
    (mem_normalizer_iff.1 (lin_L₁_le_normalizer_Kc hl k c hg') y).1 hy, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem lin_centerIn_D : CFSG.centerIn d.D = d.F := (k.s9_2 c.S c.S_syl c.P_le_S).2.2.2.1

theorem lin_F_le_D : d.F ≤ d.D := s313a_F_le_D hl.toCaseHyp k c.S_syl c.P_le_S

theorem lin_D_le_centralizer_F : d.D ≤ centralizer (d.F : Set G) :=
  s313a_D_le_centralizer_F hl.toCaseHyp k c.S_syl c.P_le_S

theorem lin_mul_self_mem_F : ∀ x ∈ d.D, x * x ∈ d.F := (k.s9_2 c.S c.S_syl c.P_le_S).2.2.2.2

theorem lin_commutator_mem_F {a b : G} (ha : a ∈ d.D) (hb : b ∈ d.D) :
    a * b * a⁻¹ * b⁻¹ ∈ d.F :=
  s313a_commutatorElement_mem_F hl.toCaseHyp k c.S_syl c.P_le_S ha hb

theorem lin_L₁_le_normalizer_F : d.L₁ ≤ normalizer (d.F : Set G) :=
  s313a_L₁_le_normalizer_F hl.toCaseHyp k c.S_syl c.P_le_S

theorem lin_L₁_le_normalizer_D : d.L₁ ≤ normalizer (d.D : Set G) := hl.hyp.L₁_le_normalizer_D

theorem lin_D_le_S : d.D ≤ c.S := s313a_D_le_S hl.toCaseHyp k c.S_syl c.P_le_S

theorem lin_map_conj_t_F : d.F.map (MulAut.conj d.t).toMonoidHom = d.F :=
  map_conj_eq_of_mem_normalizer hl.hyp.t_mem_normalizer_F

theorem lin_map_conj_t_D : d.D.map (MulAut.conj d.t).toMonoidHom = d.D :=
  map_conj_eq_of_mem_normalizer hl.hyp.t_mem_normalizer_D

theorem lin_card_F : Nat.card d.F = (2 ^ f) ^ 8 := hl.hyp.card_F hl.gms

theorem lin_isElementaryAbelian_F : CFSG.IsElementaryAbelian 2 d.F :=
  hl.hyp.isElementaryAbelian_F hl.gms

end CaseBData

end Data

end CFSG.LocalAnalysis.EvenBN.U5
