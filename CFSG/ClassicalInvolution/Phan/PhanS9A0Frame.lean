module

public import CFSG.ClassicalInvolution.Phan.PhanS7Def
import all CFSG.ClassicalInvolution.Phan.PhanH5Frames
public import CFSG.ClassicalInvolution.Phan.PhanS7Ctx

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.A0

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.PhanB3.H
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

section FrameGen

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {Q : QuadraticForm k V}

theorem La_e₁ (Fr : Frame Q) (A : SL(2, k)) :
    Fr.La A Fr.e₁ = (A : Matrix (Fin 2) (Fin 2) k) 0 0 • Fr.e₁ +
      (A : Matrix (Fin 2) (Fin 2) k) 1 0 • Fr.f₂ := by
  have h : Fr.e₁ = Fr.incl !![1, 0; 0, 0] := by simp [Frame.incl_apply]
  conv_lhs => rw [h]
  rw [Frame.La_apply_incl]
  simp [Frame.incl_apply, Matrix.mul_apply, Fin.sum_univ_two]

theorem La_f₁ (Fr : Frame Q) (A : SL(2, k)) :
    Fr.La A Fr.f₁ = (A : Matrix (Fin 2) (Fin 2) k) 1 1 • Fr.f₁ -
      (A : Matrix (Fin 2) (Fin 2) k) 0 1 • Fr.e₂ := by
  have h : Fr.f₁ = Fr.incl !![0, 0; 0, 1] := by simp [Frame.incl_apply]
  conv_lhs => rw [h]
  rw [Frame.La_apply_incl]
  simp [Frame.incl_apply, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]

theorem La_e₂ (Fr : Frame Q) (A : SL(2, k)) :
    Fr.La A Fr.e₂ = (A : Matrix (Fin 2) (Fin 2) k) 0 0 • Fr.e₂ -
      (A : Matrix (Fin 2) (Fin 2) k) 1 0 • Fr.f₁ := by
  have h : Fr.e₂ = Fr.incl !![0, -1; 0, 0] := by simp [Frame.incl_apply]
  conv_lhs => rw [h]
  rw [Frame.La_apply_incl]
  simp [Frame.incl_apply, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]
  abel

theorem La_f₂ (Fr : Frame Q) (A : SL(2, k)) :
    Fr.La A Fr.f₂ = (A : Matrix (Fin 2) (Fin 2) k) 0 1 • Fr.e₁ +
      (A : Matrix (Fin 2) (Fin 2) k) 1 1 • Fr.f₂ := by
  have h : Fr.f₂ = Fr.incl !![0, 0; 1, 0] := by simp [Frame.incl_apply]
  conv_lhs => rw [h]
  rw [Frame.La_apply_incl]
  simp [Frame.incl_apply, Matrix.mul_apply, Fin.sum_univ_two]

end FrameGen

section Emb

variable {F K : Type} [Field F] [Field K] [Algebra F K]

theorem emb_add (a b : W7 F) : emb (K := K) (a + b) = emb a + emb b := by
  funext s
  simp [emb]

theorem emb_sub (a b : W7 F) : emb (K := K) (a - b) = emb a - emb b := by
  funext s
  simp [emb]

theorem emb_smul (c : F) (a : W7 F) : emb (K := K) (c • a) = algebraMap F K c • emb a := by
  funext s
  simp [emb]

theorem emb_mk7 (x0 x1 x2 y0 y1 y2 z : F) :
    emb (K := K) (mk7 x0 x1 x2 y0 y1 y2 z) = mk7 (algebraMap F K x0) (algebraMap F K x1)
      (algebraMap F K x2) (algebraMap F K y0) (algebraMap F K y1) (algebraMap F K y2)
      (algebraMap F K z) := by
  funext s
  rcases s with i | i | ⟨⟩
  · fin_cases i <;> simp [emb, mk7]
  · fin_cases i <;> simp [emb, mk7]
  · simp [emb, mk7]

theorem alg_two : algebraMap F K (2 : F) = 2 := map_ofNat _ 2

theorem two_ne_zero_of (h2 : (2 : F) ≠ 0) : (2 : K) ≠ 0 := by
  intro h
  apply h2
  apply (algebraMap F K).injective
  rw [alg_two, h, map_zero]

theorem fr0_f₁ (h2 : (2 : F) ≠ 0) :
    (fr0 h2).f₁ = mk7 (1 / 2) (-(1 / 2)) 0 (1 / 2) (1 / 2) 0 0 := by
  simp [fr0, hyp0, HypFrame.toFrame, Frame.f₁]

theorem fr0_f₂ (h2 : (2 : F) ≠ 0) :
    (fr0 h2).f₂ = mk7 0 0 (1 / 2) 0 0 (-(1 / 2)) (1 / 2) := by
  simp [fr0, hyp0, HypFrame.toFrame, Frame.f₂]

@[expose] noncomputable def iK (h2 : (2 : F) ≠ 0) : Matrix (Fin 2) (Fin 2) K →ₗ[K] W7 K where
  toFun X := X 0 0 • emb (fr0 h2).e₁ + X 1 1 • emb (fr0 h2).f₁ + (-X 0 1) • emb (fr0 h2).e₂ +
    X 1 0 • emb (fr0 h2).f₂
  map_add' X Y := by
    simp only [Matrix.add_apply, add_smul, neg_add]
    abel
  map_smul' c X := by
    simp only [Matrix.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add,
      neg_smul, smul_neg]

theorem iK_apply (h2 : (2 : F) ≠ 0) (X : Matrix (Fin 2) (Fin 2) K) :
    iK h2 X = X 0 0 • emb (fr0 h2).e₁ + X 1 1 • emb (fr0 h2).f₁ + (-X 0 1) • emb (fr0 h2).e₂ +
      X 1 0 • emb (fr0 h2).f₂ := rfl

theorem extK_La0_iK (h2 : (2 : F) ≠ 0) (A : SL(2, F)) (X : Matrix (Fin 2) (Fin 2) K) :
    extK (La0 h2 A).toLinearMap (iK h2 X) =
      iK h2 ((A : Matrix (Fin 2) (Fin 2) F).map (algebraMap F K) * X) := by
  simp only [iK_apply, map_add, map_smul, extK_emb, LinearEquiv.coe_coe]
  rw [La0, La_e₁, La_f₁, La_e₂, La_f₂]
  simp only [emb_add, emb_sub, emb_smul, smul_add, smul_sub]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]
  module

variable (D : KDat F K)

theorem vXi_eq_iK (h2 : (2 : F) ≠ 0) : vXi D = iK h2 !![1, -D.θ; D.θ, 1] := by
  have h : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ (two_ne_zero_of h2)
  rw [iK_apply, fr0_e₁_eq, fr0_f₁, fr0_e₂_eq, fr0_f₂]
  simp only [emb_mk7]
  funext s
  rcases s with i | i | ⟨⟩
  · fin_cases i
    all_goals simp [vXi, mk7, alg_two]
    all_goals linear_combination (-1) * h
  · fin_cases i
    all_goals simp [vXi, mk7, alg_two]
    all_goals linear_combination (-1) * h
  · simp [vXi, mk7, alg_two]
    linear_combination (-D.θ) * h

theorem vE2_eq_iK (h2 : (2 : F) ≠ 0) : vE2 D = iK h2 !![1, -D.θ; -D.θ, -1] := by
  have h : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ (two_ne_zero_of h2)
  rw [iK_apply, fr0_e₁_eq, fr0_f₁, fr0_e₂_eq, fr0_f₂]
  simp only [emb_mk7]
  funext s
  rcases s with i | i | ⟨⟩
  · fin_cases i
    all_goals simp [vE2, mk7, alg_two]
    all_goals first | linear_combination (-1) * h | linear_combination D.θ * h
  · fin_cases i
    all_goals simp [vE2, mk7, alg_two]
    all_goals first | linear_combination h | linear_combination (-D.θ) * h
  · simp [vE2, mk7, alg_two]

theorem vE3_eq_emb :
    vE3 D = emb (mk7 (0 : F) 1 0 0 1 0 0) + D.θ • emb (mk7 (0 : F) 0 1 0 0 1 0) := by
  simp only [emb_mk7]
  funext s
  rcases s with i | i | ⟨⟩
  · fin_cases i <;> simp [vE3, mk7]
  · fin_cases i <;> simp [vE3, mk7]
  · simp [vE3, mk7]

theorem coords_perp₁ (h2 : (2 : F) ≠ 0) : (fr0 h2).coords (mk7 0 1 0 0 1 0 0) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Frame.coords_apply, fr0_e₁_eq, fr0_e₂_eq, fr0_f₁, fr0_f₂, polar_mk7]

theorem coords_perp₂ (h2 : (2 : F) ≠ 0) : (fr0 h2).coords (mk7 0 0 1 0 0 1 0) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Frame.coords_apply, fr0_e₁_eq, fr0_e₂_eq, fr0_f₁, fr0_f₂, polar_mk7]

theorem coords_P (h2 : (2 : F) ≠ 0) (s z : F) :
    (fr0 h2).coords (mk7 s 0 0 s 0 0 z) = !![s, -z; z, s] := by
  have h : (2 : F) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [Frame.coords_apply, fr0_e₁_eq, fr0_e₂_eq, fr0_f₁, fr0_f₂, polar_mk7]
  all_goals first | linear_combination s * h | linear_combination z * h

theorem theta_ne : D.θ ≠ 0 := by
  intro h
  have h1 : (-1 : K) = 0 := by rw [← D.theta_sq, h]; ring
  exact one_ne_zero (neg_eq_zero.mp h1)

end Emb

end CFSG.ClassicalInvolution.PhanB3.S.A0
