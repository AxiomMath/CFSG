module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Klein
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Quat

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open Matrix CFSG.Open

variable {K : Type} [Field K]

@[expose] def mS : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

@[expose] def mT (a b : K) : Matrix (Fin 2) (Fin 2) K := !![a, b; b, -a]

theorem quatRel_ST {a b : K} (hab : a ^ 2 + b ^ 2 = -1) :
    QuatRel (mS : Matrix (Fin 2) (Fin 2) K) (mT a b) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [mS, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [mT, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hab
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [mS, mT, Matrix.mul_apply, Fin.sum_univ_two]

section Elements

variable {a b half : K}

@[expose] def mC2 (a b half : K) : Matrix (Fin 2) (Fin 2) K := quatC half mS (mT a b)

theorem mC2_cubed (hab : a ^ 2 + b ^ 2 = -1) (hh : (2 : K) * half = 1) :
    mC2 a b half * mC2 a b half * mC2 a b half = 1 :=
  (quatRel_ST hab).c_cubed hh

@[expose] def gS (hab : a ^ 2 + b ^ 2 = -1) : GL (Fin 2) K :=
  ⟨mS, -mS, by rw [mul_neg, (quatRel_ST hab).ss, neg_neg],
    by rw [neg_mul, (quatRel_ST hab).ss, neg_neg]⟩

@[expose] def gT (hab : a ^ 2 + b ^ 2 = -1) : GL (Fin 2) K :=
  ⟨mT a b, -mT a b, by rw [mul_neg, (quatRel_ST hab).tt, neg_neg],
    by rw [neg_mul, (quatRel_ST hab).tt, neg_neg]⟩

@[expose] def gC (hab : a ^ 2 + b ^ 2 = -1) (hh : (2 : K) * half = 1) : GL (Fin 2) K :=
  ⟨mC2 a b half, mC2 a b half * mC2 a b half, by
    rw [← mul_assoc]; exact mC2_cubed hab hh,
    mC2_cubed hab hh⟩

theorem det_mS : (mS : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  simp [mS, det_fin_two]

theorem det_mT (hab : a ^ 2 + b ^ 2 = -1) : (mT a b).det = 1 := by
  simp [mT, det_fin_two]
  linear_combination -hab

theorem det_mC2 (hab : a ^ 2 + b ^ 2 = -1) (hh : (2 : K) * half = 1) :
    (mC2 a b half).det = 1 := by
  unfold mC2 quatC
  rw [Matrix.det_smul]
  simp [det_fin_two, mS, mT]
  linear_combination (-2 * half ^ 2) * hab + (2 * half + 1) * hh

theorem glScalar_neg_one {ι : Type} [Fintype ι] [DecidableEq ι] :
    ((Matrix.GeneralLinearGroup.scalar ι (-1 : Kˣ) : GL ι K) : Matrix ι ι K) = -1 := by
  rw [GeneralLinearGroup.coe_scalar]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem glScalar_one {ι : Type} [Fintype ι] [DecidableEq ι] :
    Matrix.GeneralLinearGroup.scalar ι (1 : Kˣ) = (1 : GL ι K) := map_one _

theorem threeTwoWitness_psl_two_odd [Finite K] (h2 : (2 : K) ≠ 0) (hodd : Nat.card K % 2 = 1) :
    ThreeTwoWitness (StatedProj (StatedSL 2 K)) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨a, b, hab0⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2 + Polynomial.C (1 : K)) (g := Polynomial.X ^ 2)
    (by rw [Polynomial.degree_X_pow_add_C (by norm_num)]; norm_num)
    (by rw [Polynomial.degree_X_pow]; norm_num)
    (by rw [← Nat.card_eq_fintype_card]; exact hodd)
  have hab : a ^ 2 + b ^ 2 = -1 := by
    simp at hab0
    linear_combination hab0
  set half : K := (2 : K)⁻¹ with hhalf
  have hh : (2 : K) * half = 1 := mul_inv_cancel₀ h2
  have hrel := quatRel_ST (K := K) hab
  have hS : gS hab ∈ StatedSL 2 K := Subgroup.subset_closure det_mS
  have hT : gT hab ∈ StatedSL 2 K := Subgroup.subset_closure (det_mT hab)
  have hC : gC hab hh ∈ StatedSL 2 K := Subgroup.subset_closure (det_mC2 hab hh)
  refine threeTwoWitness_statedProj_klein_mod (gT hab) (gS hab) (gC hab hh) hT hS hC
    ⟨-1, Units.ext ?_⟩ ⟨-1, Units.ext ?_⟩ ⟨-1, Units.ext ?_⟩ ?_ ⟨1, Units.ext ?_⟩ ?_
    ⟨1, Units.ext ?_⟩ ⟨-1, Units.ext ?_⟩
  · show mT a b * mT a b = _
    rw [hrel.tt, glScalar_neg_one]
  · show mS * mS = _
    rw [hrel.ss, glScalar_neg_one]
  · show mT a b * mS = _
    rw [Units.val_mul, glScalar_neg_one, neg_one_mul]
    exact hrel.ts
  · intro u hu
    have e00 := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) hu
    have e11 := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 1 1) hu
    have e01 := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 1) hu
    simp [gT, mT, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at e00 e11 e01
    have h2a : (2 : K) * a = 0 := by linear_combination e11 - e00
    have ha : a = 0 := (mul_eq_zero.1 h2a).resolve_left h2
    have hb : b = 0 := e01.symm
    have : (-1 : K) = 0 := by rw [← hab, ha, hb]; ring
    exact one_ne_zero (neg_eq_zero.1 this)
  · rw [glScalar_one, Units.val_one, Units.val_pow_eq_pow_val]
    show mC2 a b half ^ 3 = 1
    rw [pow_succ, pow_two]
    exact mC2_cubed hab hh
  · intro u hu
    have e01 := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 1) hu
    have e10 := congrArg (fun A : GL (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 1 0) hu
    simp [gC, mC2, quatC, mS, mT, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply] at e01 e10
    have h0 : (2 : K) * half = 0 := by linear_combination e10 - e01
    exact one_ne_zero (hh.symm.trans h0)
  · show mC2 a b half * mT a b * (mC2 a b half * mC2 a b half) = _
    rw [glScalar_one, Units.val_mul, Units.val_one, one_mul]
    show _ = mS
    have h1 := hrel.c_t half
    calc mC2 a b half * mT a b * (mC2 a b half * mC2 a b half)
        = mS * (mC2 a b half * mC2 a b half * mC2 a b half) := by
          rw [show mC2 a b half * mT a b = mS * mC2 a b half from h1, mul_assoc]
          simp only [mul_assoc]
      _ = mS := by rw [mC2_cubed hab hh, mul_one]
  · show mC2 a b half * mS * (mC2 a b half * mC2 a b half) = _
    rw [Units.val_mul, glScalar_neg_one, neg_one_mul, Units.val_mul]
    show _ = -(mT a b * mS)
    have h1 := hrel.c_s half
    calc mC2 a b half * mS * (mC2 a b half * mC2 a b half)
        = (mS * mT a b) * (mC2 a b half * mC2 a b half * mC2 a b half) := by
          rw [show mC2 a b half * mS = mS * mT a b * mC2 a b half from h1]
          simp only [mul_assoc]
      _ = mS * mT a b := by rw [mC2_cubed hab hh, mul_one]
      _ = -(mT a b * mS) := by rw [hrel.ts, neg_neg]

end Elements

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
