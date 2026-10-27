module

public import CFSG.CGT.Stroth77.Extension218Basic
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations

public section

namespace CFSG.CGT.Stroth77

namespace Ext218

open Matrix

variable {s : ℕ} {i F G : ℤ}

local macro "simp_t221" : tactic =>
  `(tactic| simp only [Type221.action, SigmaFourAction.ofMatEq, Type221.k, Type221.uvM,
    Type221.tM, Type221.uvA, Type221.ρM, Type221.uM, uMat, ofCols_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul])

theorem phiU_gen0_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φu
        ((1 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
          (0 : ℤ) • gen (Type221.k s) 2) =
      (-1 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
        (0 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG

theorem phiR_gen0_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φρ
        ((1 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
          (0 : ℤ) • gen (Type221.k s) 2) =
      (1 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
        (0 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG

theorem phiT_gen0_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φt
        ((1 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
          (0 : ℤ) • gen (Type221.k s) 2) =
      (-8 * G - 15 : ℤ) • gen (Type221.k s) 0 + (4 : ℤ) • gen (Type221.k s) 1 +
        (8 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG

theorem phiUV_gen0_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φuv
        ((1 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
          (0 : ℤ) • gen (Type221.k s) 2) =
      (-8 * G - 19 : ℤ) • gen (Type221.k s) 0 + (4 : ℤ) • gen (Type221.k s) 1 +
        (-4 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG

theorem phiR_cS_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φρ
        ((2 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
          (0 : ℤ) • gen (Type221.k s) 2) =
      (2 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
        (0 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG

theorem phiR_aS_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φρ
        ((0 : ℤ) • gen (Type221.k s) 0 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 1 +
          (0 : ℤ) • gen (Type221.k s) 2) =
      (0 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
        (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG

theorem phiR_bS_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φρ
        ((0 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
          (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 2) =
      (0 : ℤ) • gen (Type221.k s) 0 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 1 +
        (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (-2 : ℤ))
    (t1 := (-1 : ℤ))
    (t2 := (-1 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG

theorem phiU_cS_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φu
        ((2 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
          (0 : ℤ) • gen (Type221.k s) 2) =
      (2 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
        (0 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (-1 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG

theorem phiU_aS_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φu
        ((0 : ℤ) • gen (Type221.k s) 0 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 1 +
          (0 : ℤ) • gen (Type221.k s) 2) =
      (0 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
        (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 1 0 0
    (t0 := (-1024 * ((2 : ℤ) ^ s) ^ 2 + 4 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (-64 * (2 : ℤ) ^ s) * hG
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG

theorem phiU_bS_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φu
        ((0 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
          (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 2) =
      (0 : ℤ) • gen (Type221.k s) 0 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 1 +
        (0 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 1 0 0
    (t0 := (-1024 * ((2 : ℤ) ^ s) ^ 2 + 4 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (-64 * (2 : ℤ) ^ s) * hG
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG

theorem phiT_cS_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φt
        ((2 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
          (0 : ℤ) • gen (Type221.k s) 2) =
      (2 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 0 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 1 +
        (0 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 1 0 0
    (t0 := (-256 * ((2 : ℤ) ^ s) ^ 2 + 4 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (1 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (-16 * (2 : ℤ) ^ s) * hG
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG

theorem phiT_aS_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φt
        ((0 : ℤ) • gen (Type221.k s) 0 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 1 +
          (0 : ℤ) • gen (Type221.k s) 2) =
      (0 : ℤ) • gen (Type221.k s) 0 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 1 +
        (0 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 2 1 1
    (t0 := (131072 * ((2 : ℤ) ^ s) ^ 4 - 14080 * ((2 : ℤ) ^ s) ^ 2 - 28 : ℤ))
    (t1 := (-1792 * ((2 : ℤ) ^ s) ^ 2 + 12 * (2 : ℤ) ^ s - 5 : ℤ))
    (t2 := (-2048 * ((2 : ℤ) ^ s) ^ 2 - 4 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (8192 * ((2 : ℤ) ^ s) ^ 3 + 384 * G * (2 : ℤ) ^ s + 16 * (2 : ℤ) ^ s) * hG
  · simp_t221
    linear_combination (-448 * (2 : ℤ) ^ s) * hG
  · simp_t221
    linear_combination (-512 * (2 : ℤ) ^ s) * hG

theorem phiT_bS_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φt
        ((0 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
          (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 2) =
      (0 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
        (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 2 1 1
    (t0 := (262144 * ((2 : ℤ) ^ s) ^ 4 - 6656 * ((2 : ℤ) ^ s) ^ 2 - 144 * (2 : ℤ) ^ s - 14 : ℤ))
    (t1 := (-512 * ((2 : ℤ) ^ s) ^ 2 - 12 * (2 : ℤ) ^ s - 1 : ℤ))
    (t2 := (-1792 * ((2 : ℤ) ^ s) ^ 2 - 12 * (2 : ℤ) ^ s - 5 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (16384 * ((2 : ℤ) ^ s) ^ 3 + 768 * G * (2 : ℤ) ^ s +
      1376 * (2 : ℤ) ^ s) * hG
  · simp_t221
    linear_combination (-128 * (2 : ℤ) ^ s) * hG
  · simp_t221
    linear_combination (-448 * (2 : ℤ) ^ s) * hG

theorem phiUV_cS_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φuv
        ((2 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
          (0 : ℤ) • gen (Type221.k s) 2) =
      (2 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 0 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 1 +
        (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 1 0 0
    (t0 := (-256 * ((2 : ℤ) ^ s) ^ 2 - 2 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (-1 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (-16 * (2 : ℤ) ^ s) * hG
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG

theorem phiUV_aS_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φuv
        ((0 : ℤ) • gen (Type221.k s) 0 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 1 +
          (0 : ℤ) • gen (Type221.k s) 2) =
      (0 : ℤ) • gen (Type221.k s) 0 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 1 +
        (0 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 2 1 1
    (t0 := (262144 * ((2 : ℤ) ^ s) ^ 4 - 512 * ((2 : ℤ) ^ s) ^ 2 - 2 : ℤ))
    (t1 := (-1280 * ((2 : ℤ) ^ s) ^ 2 - 4 : ℤ))
    (t2 := (512 * ((2 : ℤ) ^ s) ^ 2 + 12 * (2 : ℤ) ^ s + 1 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (16384 * ((2 : ℤ) ^ s) ^ 3 + 768 * G * (2 : ℤ) ^ s +
      1760 * (2 : ℤ) ^ s) * hG
  · simp_t221
    linear_combination (-320 * (2 : ℤ) ^ s) * hG
  · simp_t221
    linear_combination (128 * (2 : ℤ) ^ s) * hG

theorem phiUV_bS_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φuv
        ((0 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
          (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 2) =
      (0 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
        (8 * (2 : ℤ) ^ s : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 2 1 1
    (t0 := (-67108864 * ((2 : ℤ) ^ s) ^ 6 + 2097152 * ((2 : ℤ) ^ s) ^ 5 -
      4980736 * ((2 : ℤ) ^ s) ^ 4 + 118784 * ((2 : ℤ) ^ s) ^ 3 - 12544 * ((2 : ℤ) ^ s) ^ 2 +
      224 * (2 : ℤ) ^ s - 6 : ℤ))
    (t1 := (-1310720 * ((2 : ℤ) ^ s) ^ 4 + 18432 * ((2 : ℤ) ^ s) ^ 3 - 4000 * ((2 : ℤ) ^ s) ^ 2 +
      36 * (2 : ℤ) ^ s - 3 : ℤ))
    (t2 := (131072 * ((2 : ℤ) ^ s) ^ 4 + 1024 * ((2 : ℤ) ^ s) ^ 2 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (-4194304 * ((2 : ℤ) ^ s) ^ 5 - 196608 * G * ((2 : ℤ) ^ s) ^ 3 +
      131072 * ((2 : ℤ) ^ s) ^ 4 - 9216 * G ^ 2 * (2 : ℤ) ^ s + 6144 * G * ((2 : ℤ) ^ s) ^ 2 -
      770048 * ((2 : ℤ) ^ s) ^ 3 - 57600 * G * (2 : ℤ) ^ s + 21760 * ((2 : ℤ) ^ s) ^ 2 -
      85008 * (2 : ℤ) ^ s) * hG
  · simp_t221
    linear_combination (-327680 * ((2 : ℤ) ^ s) ^ 3 - 15360 * G * (2 : ℤ) ^ s +
      4608 * ((2 : ℤ) ^ s) ^ 2 - 36864 * (2 : ℤ) ^ s) * hG
  · simp_t221
    linear_combination (32768 * ((2 : ℤ) ^ s) ^ 3 + 1536 * G * (2 : ℤ) ^ s +
      3840 * (2 : ℤ) ^ s) * hG

theorem phiUV_baseUV_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φuv
        ((-4 * G - 10 : ℤ) • gen (Type221.k s) 0 + (2 : ℤ) • gen (Type221.k s) 1 +
          (-2 : ℤ) • gen (Type221.k s) 2) =
      (4 * G + 10 : ℤ) • gen (Type221.k s) 0 + (-2 : ℤ) • gen (Type221.k s) 1 +
        (2 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 2 1 1
    (t0 := (16777216 * ((2 : ℤ) ^ s) ^ 5 - 524288 * ((2 : ℤ) ^ s) ^ 4 +
      1343488 * ((2 : ℤ) ^ s) ^ 3 - 29696 * ((2 : ℤ) ^ s) ^ 2 + 3136 * (2 : ℤ) ^ s - 56 : ℤ))
    (t1 := (327680 * ((2 : ℤ) ^ s) ^ 3 - 4608 * ((2 : ℤ) ^ s) ^ 2 + 616 * (2 : ℤ) ^ s - 9 : ℤ))
    (t2 := (-32768 * ((2 : ℤ) ^ s) ^ 3 - 64 * (2 : ℤ) ^ s + 3 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (1048576 * ((2 : ℤ) ^ s) ^ 4 + 49152 * G * ((2 : ℤ) ^ s) ^ 2 -
      32768 * ((2 : ℤ) ^ s) ^ 3 + 2304 * G ^ 2 - 1536 * G * (2 : ℤ) ^ s +
      198656 * ((2 : ℤ) ^ s) ^ 2 + 14688 * G - 5440 * (2 : ℤ) ^ s + 21924) * hG
  · simp_t221
    linear_combination (81920 * ((2 : ℤ) ^ s) ^ 2 + 3840 * G - 1152 * (2 : ℤ) ^ s + 9120) * hG
  · simp_t221
    linear_combination (-8192 * ((2 : ℤ) ^ s) ^ 2 - 384 * G - 912) * hG

theorem phiT_baseT_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φt
        ((-4 * G - 8 : ℤ) • gen (Type221.k s) 0 + (2 : ℤ) • gen (Type221.k s) 1 +
          (4 : ℤ) • gen (Type221.k s) 2) =
      (4 * G + 8 : ℤ) • gen (Type221.k s) 0 + (-2 : ℤ) • gen (Type221.k s) 1 +
        (-4 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 1 0 0
    (t0 := (65536 * ((2 : ℤ) ^ s) ^ 3 - 2752 * (2 : ℤ) ^ s - 24 : ℤ))
    (t1 := (-256 * (2 : ℤ) ^ s - 1 : ℤ))
    (t2 := (-512 * (2 : ℤ) ^ s - 2 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (4096 * ((2 : ℤ) ^ s) ^ 2 + 192 * G + 276) * hG
  · simp_t221
    linear_combination (-64) * hG
  · simp_t221
    linear_combination (-128) * hG

theorem phiU_baseUV_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φu
        ((-4 * G - 10 : ℤ) • gen (Type221.k s) 0 + (2 : ℤ) • gen (Type221.k s) 1 +
          (-2 : ℤ) • gen (Type221.k s) 2) =
      (4 * G + 10 : ℤ) • gen (Type221.k s) 0 + (-2 : ℤ) • gen (Type221.k s) 1 +
        (2 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG

theorem phiUV_baseU_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φuv
        ((-1 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
          (0 : ℤ) • gen (Type221.k s) 2) =
      (8 * G + 19 : ℤ) • gen (Type221.k s) 0 + (-4 : ℤ) • gen (Type221.k s) 1 +
        (4 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG

theorem phiR_baseT_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φρ
        ((-4 * G - 8 : ℤ) • gen (Type221.k s) 0 + (2 : ℤ) • gen (Type221.k s) 1 +
          (4 : ℤ) • gen (Type221.k s) 2) =
      (-4 * G - 12 : ℤ) • gen (Type221.k s) 0 + (-4 : ℤ) • gen (Type221.k s) 1 +
        (-2 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG

theorem phiT_baseUV_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φt
        ((-4 * G - 10 : ℤ) • gen (Type221.k s) 0 + (2 : ℤ) • gen (Type221.k s) 1 +
          (-2 : ℤ) • gen (Type221.k s) 2) =
      (-4 : ℤ) • gen (Type221.k s) 0 + (-6 : ℤ) • gen (Type221.k s) 1 +
        (-6 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (-256 * (2 : ℤ) ^ s + 4 : ℤ))
    (t1 := (-128 * (2 : ℤ) ^ s + 2 : ℤ))
    (t2 := (-64 * (2 : ℤ) ^ s + 1 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (-16) * hG
  · simp_t221
    linear_combination (-32) * hG
  · simp_t221
    linear_combination (-16) * hG

theorem phiU_baseU_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φu
        ((-1 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
          (0 : ℤ) • gen (Type221.k s) 2) =
      (1 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
        (0 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG

theorem phiR_baseU_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φρ
        ((-1 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
          (0 : ℤ) • gen (Type221.k s) 2) =
      (-1 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
        (0 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG
  · simp_t221
    linear_combination (0) * hG

end Ext218

end CFSG.CGT.Stroth77
