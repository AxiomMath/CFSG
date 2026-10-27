module

public import CFSG.CGT.Stroth77.Extension218Torus

public section

namespace CFSG.CGT.Stroth77

namespace Ext218

open Matrix

variable {s : ℕ} {i F G N K J : ℤ}

theorem gen_zero_eq218 {k : Fin 3 → ℕ} :
    gen k 0 = (1 : ℤ) • gen k 0 + (0 : ℤ) • gen k 1 + (0 : ℤ) • gen k 2 := by
  simp

theorem gen_one_eq218 {k : Fin 3 → ℕ} :
    gen k 1 = (0 : ℤ) • gen k 0 + (1 : ℤ) • gen k 1 + (0 : ℤ) • gen k 2 := by
  simp

theorem gen_two_eq218 {k : Fin 3 → ℕ} :
    gen k 2 = (0 : ℤ) • gen k 0 + (0 : ℤ) • gen k 1 + (1 : ℤ) • gen k 2 := by
  simp

local macro "simp_t221" : tactic =>
  `(tactic| simp only [Type221.action, SigmaFourAction.ofMatEq, Type221.k, Type221.uvM,
    Type221.tM, Type221.uvA, Type221.ρM, Type221.uM, uMat, ofCols_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul])

local macro "simp_t121" : tactic =>
  `(tactic| simp only [Type121.action, SigmaFourAction.ofMatEq, Type121.k, Type121.uvM,
    Type121.tM, Type121.uvA, Type121.ρM, Type121.uM, uMat, ofCols_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul])

local macro "simp_t131" : tactic =>
  `(tactic| simp only [Type131.action, SigmaFourAction.ofMatEq, Type131.k, Type131.uvM,
    Type131.tM, Type131.uvA, Type131.ρM, Type131.uM, uMat, ofCols_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul])

theorem phiUV_gen1_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φuv (gen (Type221.k s) 1) =
      (32 * G ^ 2 + 148 * G + 171 : ℤ) • gen (Type221.k s) 0 +
        (-40 * G - 95 : ℤ) • gen (Type221.k s) 1 +
        (16 * G + 8 * (2 : ℤ) ^ s + 38 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  conv_lhs => rw [gen_one_eq218]
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

theorem phiUV_gen2_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φuv (gen (Type221.k s) 2) =
      (-384 * G ^ 3 + 256 * G ^ 2 * (2 : ℤ) ^ s - 3296 * G ^ 2 + 1504 * G * (2 : ℤ) ^ s - 9142 * G +
          2128 * (2 : ℤ) ^ s - 8265 : ℤ) • gen (Type221.k s) 0 +
        (-1920 * G ^ 2 + 576 * G * (2 : ℤ) ^ s + 64 * ((2 : ℤ) ^ s) ^ 2 - 9088 * G +
            1368 * (2 : ℤ) ^ s - 10754 : ℤ) • gen (Type221.k s) 1 +
        (192 * G ^ 2 + 928 * G + 1121 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  conv_lhs => rw [gen_two_eq218]
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

theorem phiT_gen1_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φt (gen (Type221.k s) 1) =
      (16 * G ^ 2 + 38 * G : ℤ) • gen (Type221.k s) 0 +
        (-56 * G + 8 * (2 : ℤ) ^ s - 133 : ℤ) • gen (Type221.k s) 1 +
        (-64 * G - 152 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  conv_lhs => rw [gen_one_eq218]
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

theorem phiT_gen2_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φt (gen (Type221.k s) 2) =
      (32 * G ^ 2 + 132 * G - 8 * (2 : ℤ) ^ s + 133 : ℤ) • gen (Type221.k s) 0 +
        (-16 * G - 8 * (2 : ℤ) ^ s - 38 : ℤ) • gen (Type221.k s) 1 +
        (-56 * G - 8 * (2 : ℤ) ^ s - 133 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  conv_lhs => rw [gen_two_eq218]
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

theorem phiU_gen1_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φu (gen (Type221.k s) 1) =
      (-8 * G - 18 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
        (1 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  conv_lhs => rw [gen_one_eq218]
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

theorem phiU_gen2_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φu (gen (Type221.k s) 2) =
      (-8 * G - 18 : ℤ) • gen (Type221.k s) 0 + (1 : ℤ) • gen (Type221.k s) 1 +
        (0 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  conv_lhs => rw [gen_two_eq218]
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

theorem phiR_gen1_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φρ (gen (Type221.k s) 1) =
      (0 : ℤ) • gen (Type221.k s) 0 + (0 : ℤ) • gen (Type221.k s) 1 +
        (1 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  conv_lhs => rw [gen_one_eq218]
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

theorem phiR_gen2_t221 (h : Type221.Data s i F G) :
    (Type221.action h).φρ (gen (Type221.k s) 2) =
      (-1 : ℤ) • gen (Type221.k s) 0 + (-1 : ℤ) • gen (Type221.k s) 1 +
        (-1 : ℤ) • gen (Type221.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  conv_lhs => rw [gen_two_eq218]
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

theorem phiUV_gen0_t121_t221 (h : Type121.Data (s + 3) i F G N K) :
    (Type121.action h).φuv (gen (Type121.k (s + 3)) 0) =
      (-8 * G - 19 : ℤ) • gen (Type121.k (s + 3)) 0 + (2 : ℤ) • gen (Type121.k (s + 3)) 1 +
        (-2 : ℤ) • gen (Type121.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, -, hG⟩ := h
  subst hi hF hN
  conv_lhs => rw [gen_zero_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG

theorem phiUV_gen1_t121_t221 (h : Type121.Data (s + 3) i F G N K) :
    (Type121.action h).φuv (gen (Type121.k (s + 3)) 1) =
      (2 * (32 * G ^ 2 + 148 * G + 171) : ℤ) • gen (Type121.k (s + 3)) 0 +
        (-40 * G - 95 : ℤ) • gen (Type121.k (s + 3)) 1 +
        (16 * G + 8 * (2 : ℤ) ^ s + 38 : ℤ) • gen (Type121.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, -, hG⟩ := h
  subst hi hF hN
  conv_lhs => rw [gen_one_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG

theorem phiUV_gen2_t121_t221 (h : Type121.Data (s + 3) i F G N K) :
    (Type121.action h).φuv (gen (Type121.k (s + 3)) 2) =
      (2 * (-384 * G ^ 3 + 256 * G ^ 2 * (2 : ℤ) ^ s - 3296 * G ^ 2 + 1504 * G * (2 : ℤ) ^ s -
          9142 * G + 2128 * (2 : ℤ) ^ s - 8265) : ℤ) • gen (Type121.k (s + 3)) 0 +
        (-1920 * G ^ 2 + 576 * G * (2 : ℤ) ^ s + 64 * ((2 : ℤ) ^ s) ^ 2 - 9088 * G +
            1368 * (2 : ℤ) ^ s - 10754 : ℤ) • gen (Type121.k (s + 3)) 1 +
        (192 * G ^ 2 + 928 * G + 1121 : ℤ) • gen (Type121.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, -, hG⟩ := h
  subst hi hF hN
  conv_lhs => rw [gen_two_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG

theorem phiT_gen0_t121_t221 (h : Type121.Data (s + 3) i F G N K) :
    (Type121.action h).φt (gen (Type121.k (s + 3)) 0) =
      (-8 * G - 15 : ℤ) • gen (Type121.k (s + 3)) 0 + (2 : ℤ) • gen (Type121.k (s + 3)) 1 +
        (4 : ℤ) • gen (Type121.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, -, hG⟩ := h
  subst hi hF hN
  conv_lhs => rw [gen_zero_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG

theorem phiT_gen1_t121_t221 (h : Type121.Data (s + 3) i F G N K) :
    (Type121.action h).φt (gen (Type121.k (s + 3)) 1) =
      (2 * (16 * G ^ 2 + 38 * G) : ℤ) • gen (Type121.k (s + 3)) 0 +
        (-56 * G + 8 * (2 : ℤ) ^ s - 133 : ℤ) • gen (Type121.k (s + 3)) 1 +
        (-64 * G - 152 : ℤ) • gen (Type121.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, -, hG⟩ := h
  subst hi hF hN
  conv_lhs => rw [gen_one_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG

theorem phiT_gen2_t121_t221 (h : Type121.Data (s + 3) i F G N K) :
    (Type121.action h).φt (gen (Type121.k (s + 3)) 2) =
      (2 * (32 * G ^ 2 + 132 * G - 8 * (2 : ℤ) ^ s + 133) : ℤ) • gen (Type121.k (s + 3)) 0 +
        (-16 * G - 8 * (2 : ℤ) ^ s - 38 : ℤ) • gen (Type121.k (s + 3)) 1 +
        (-56 * G - 8 * (2 : ℤ) ^ s - 133 : ℤ) • gen (Type121.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, -, hG⟩ := h
  subst hi hF hN
  conv_lhs => rw [gen_two_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG

theorem phiU_gen0_t121_t221 (h : Type121.Data (s + 3) i F G N K) :
    (Type121.action h).φu (gen (Type121.k (s + 3)) 0) =
      (-1 : ℤ) • gen (Type121.k (s + 3)) 0 + (0 : ℤ) • gen (Type121.k (s + 3)) 1 +
        (0 : ℤ) • gen (Type121.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, -, hG⟩ := h
  subst hi hF hN
  conv_lhs => rw [gen_zero_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG

theorem phiU_gen1_t121_t221 (h : Type121.Data (s + 3) i F G N K) :
    (Type121.action h).φu (gen (Type121.k (s + 3)) 1) =
      (2 * (-8 * G - 18) : ℤ) • gen (Type121.k (s + 3)) 0 + (0 : ℤ) • gen (Type121.k (s + 3)) 1 +
        (1 : ℤ) • gen (Type121.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, -, hG⟩ := h
  subst hi hF hN
  conv_lhs => rw [gen_one_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG

theorem phiU_gen2_t121_t221 (h : Type121.Data (s + 3) i F G N K) :
    (Type121.action h).φu (gen (Type121.k (s + 3)) 2) =
      (2 * (-8 * G - 18) : ℤ) • gen (Type121.k (s + 3)) 0 + (1 : ℤ) • gen (Type121.k (s + 3)) 1 +
        (0 : ℤ) • gen (Type121.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, -, hG⟩ := h
  subst hi hF hN
  conv_lhs => rw [gen_two_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG

theorem phiR_gen0_t121_t221 (h : Type121.Data (s + 3) i F G N K) :
    (Type121.action h).φρ (gen (Type121.k (s + 3)) 0) =
      (1 : ℤ) • gen (Type121.k (s + 3)) 0 + (0 : ℤ) • gen (Type121.k (s + 3)) 1 +
        (0 : ℤ) • gen (Type121.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, -, hG⟩ := h
  subst hi hF hN
  conv_lhs => rw [gen_zero_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG

theorem phiR_gen1_t121_t221 (h : Type121.Data (s + 3) i F G N K) :
    (Type121.action h).φρ (gen (Type121.k (s + 3)) 1) =
      (2 * (0) : ℤ) • gen (Type121.k (s + 3)) 0 + (0 : ℤ) • gen (Type121.k (s + 3)) 1 +
        (1 : ℤ) • gen (Type121.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, -, hG⟩ := h
  subst hi hF hN
  conv_lhs => rw [gen_one_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG

theorem phiR_gen2_t121_t221 (h : Type121.Data (s + 3) i F G N K) :
    (Type121.action h).φρ (gen (Type121.k (s + 3)) 2) =
      (2 * (-1) : ℤ) • gen (Type121.k (s + 3)) 0 + (-1 : ℤ) • gen (Type121.k (s + 3)) 1 +
        (-1 : ℤ) • gen (Type121.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, -, hG⟩ := h
  subst hi hF hN
  conv_lhs => rw [gen_two_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG
  · simp_t121
    linear_combination (0) * hG

theorem phiUV_gen0_t131_t221 (h : Type131.Data (s + 3) i F G N K J) :
    (Type131.action h).φuv (gen (Type131.k (s + 3)) 0) =
      (-8 * G - 19 : ℤ) • gen (Type131.k (s + 3)) 0 +
        (8 * (2 : ℤ) ^ s + 2 : ℤ) • gen (Type131.k (s + 3)) 1 +
        (-2 : ℤ) • gen (Type131.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 4 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
  conv_lhs => rw [gen_zero_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG

theorem phiUV_gen1_t131_t221 (h : Type131.Data (s + 3) i F G N K J) :
    (Type131.action h).φuv (gen (Type131.k (s + 3)) 1) =
      (2 * (32 * G ^ 2 + 148 * G + 171) : ℤ) • gen (Type131.k (s + 3)) 0 +
        (-40 * G - 95 : ℤ) • gen (Type131.k (s + 3)) 1 +
        (16 * G + 8 * (2 : ℤ) ^ s + 38 : ℤ) • gen (Type131.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 4 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
  conv_lhs => rw [gen_one_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG

theorem phiUV_gen2_t131_t221 (h : Type131.Data (s + 3) i F G N K J) :
    (Type131.action h).φuv (gen (Type131.k (s + 3)) 2) =
      (2 * (-384 * G ^ 3 + 256 * G ^ 2 * (2 : ℤ) ^ s - 3296 * G ^ 2 + 1504 * G * (2 : ℤ) ^ s -
          9142 * G + 2128 * (2 : ℤ) ^ s - 8265) : ℤ) • gen (Type131.k (s + 3)) 0 +
        (-1920 * G ^ 2 + 576 * G * (2 : ℤ) ^ s + 64 * ((2 : ℤ) ^ s) ^ 2 - 9088 * G +
            1368 * (2 : ℤ) ^ s - 10754 : ℤ) • gen (Type131.k (s + 3)) 1 +
        (192 * G ^ 2 + 928 * G + 1121 : ℤ) • gen (Type131.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 4 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
  conv_lhs => rw [gen_two_eq218]
  refine matAct_gens_eq _ _ 2 2 2
    (t0 := (-524288 * ((2 : ℤ) ^ s) ^ 4 + 1024 * ((2 : ℤ) ^ s) ^ 2 + 4 : ℤ))
    (t1 := (-131072 * ((2 : ℤ) ^ s) ^ 4 + 256 * ((2 : ℤ) ^ s) ^ 2 + 1 : ℤ))
    (t2 := (-131072 * ((2 : ℤ) ^ s) ^ 4 + 256 * ((2 : ℤ) ^ s) ^ 2 + 1 : ℤ)) ?_ ?_ ?_
  · simp_t131
    linear_combination (-65536 * ((2 : ℤ) ^ s) ^ 3 - 3072 * G * (2 : ℤ) ^ s -
      7040 * (2 : ℤ) ^ s) * hG
  · simp_t131
    linear_combination (-32768 * ((2 : ℤ) ^ s) ^ 3 - 1536 * G * (2 : ℤ) ^ s -
      3520 * (2 : ℤ) ^ s) * hG
  · simp_t131
    linear_combination (-32768 * ((2 : ℤ) ^ s) ^ 3 - 1536 * G * (2 : ℤ) ^ s -
      3520 * (2 : ℤ) ^ s) * hG

theorem phiT_gen0_t131_t221 (h : Type131.Data (s + 3) i F G N K J) :
    (Type131.action h).φt (gen (Type131.k (s + 3)) 0) =
      (-8 * G - 15 : ℤ) • gen (Type131.k (s + 3)) 0 + (2 : ℤ) • gen (Type131.k (s + 3)) 1 +
        (8 * (2 : ℤ) ^ s + 4 : ℤ) • gen (Type131.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 4 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
  conv_lhs => rw [gen_zero_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG

theorem phiT_gen1_t131_t221 (h : Type131.Data (s + 3) i F G N K J) :
    (Type131.action h).φt (gen (Type131.k (s + 3)) 1) =
      (2 * (16 * G ^ 2 + 38 * G) : ℤ) • gen (Type131.k (s + 3)) 0 +
        (-56 * G + 8 * (2 : ℤ) ^ s - 133 : ℤ) • gen (Type131.k (s + 3)) 1 +
        (-64 * G - 152 : ℤ) • gen (Type131.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 4 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
  conv_lhs => rw [gen_one_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG

theorem phiT_gen2_t131_t221 (h : Type131.Data (s + 3) i F G N K J) :
    (Type131.action h).φt (gen (Type131.k (s + 3)) 2) =
      (2 * (32 * G ^ 2 + 132 * G - 8 * (2 : ℤ) ^ s + 133) : ℤ) • gen (Type131.k (s + 3)) 0 +
        (-16 * G - 8 * (2 : ℤ) ^ s - 38 : ℤ) • gen (Type131.k (s + 3)) 1 +
        (-56 * G - 8 * (2 : ℤ) ^ s - 133 : ℤ) • gen (Type131.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 4 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
  conv_lhs => rw [gen_two_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG

theorem phiU_gen0_t131_t221 (h : Type131.Data (s + 3) i F G N K J) :
    (Type131.action h).φu (gen (Type131.k (s + 3)) 0) =
      (4 * (2 : ℤ) ^ s - 1 : ℤ) • gen (Type131.k (s + 3)) 0 + (0 : ℤ) • gen (Type131.k (s + 3)) 1 +
        (0 : ℤ) • gen (Type131.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 4 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
  conv_lhs => rw [gen_zero_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG

theorem phiU_gen1_t131_t221 (h : Type131.Data (s + 3) i F G N K J) :
    (Type131.action h).φu (gen (Type131.k (s + 3)) 1) =
      (2 * (-8 * G - 18) : ℤ) • gen (Type131.k (s + 3)) 0 + (0 : ℤ) • gen (Type131.k (s + 3)) 1 +
        (1 : ℤ) • gen (Type131.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 4 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
  conv_lhs => rw [gen_one_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG

theorem phiU_gen2_t131_t221 (h : Type131.Data (s + 3) i F G N K J) :
    (Type131.action h).φu (gen (Type131.k (s + 3)) 2) =
      (2 * (-8 * G - 18) : ℤ) • gen (Type131.k (s + 3)) 0 + (1 : ℤ) • gen (Type131.k (s + 3)) 1 +
        (0 : ℤ) • gen (Type131.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 4 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
  conv_lhs => rw [gen_two_eq218]
  refine matAct_gens_eq _ _ 1 0 0
    (t0 := (512 * ((2 : ℤ) ^ s) ^ 2 - 2 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t131
    linear_combination (64 * (2 : ℤ) ^ s) * hG
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG

theorem phiR_gen0_t131_t221 (h : Type131.Data (s + 3) i F G N K J) :
    (Type131.action h).φρ (gen (Type131.k (s + 3)) 0) =
      (1 : ℤ) • gen (Type131.k (s + 3)) 0 + (0 : ℤ) • gen (Type131.k (s + 3)) 1 +
        (0 : ℤ) • gen (Type131.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 4 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
  conv_lhs => rw [gen_zero_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG

theorem phiR_gen1_t131_t221 (h : Type131.Data (s + 3) i F G N K J) :
    (Type131.action h).φρ (gen (Type131.k (s + 3)) 1) =
      (2 * (0) : ℤ) • gen (Type131.k (s + 3)) 0 + (0 : ℤ) • gen (Type131.k (s + 3)) 1 +
        (1 : ℤ) • gen (Type131.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 4 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
  conv_lhs => rw [gen_one_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG

theorem phiR_gen2_t131_t221 (h : Type131.Data (s + 3) i F G N K J) :
    (Type131.action h).φρ (gen (Type131.k (s + 3)) 2) =
      (2 * (-1) : ℤ) • gen (Type131.k (s + 3)) 0 + (-1 : ℤ) • gen (Type131.k (s + 3)) 1 +
        (-1 : ℤ) • gen (Type131.k (s + 3)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 4 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
  conv_lhs => rw [gen_two_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG
  · simp_t131
    linear_combination (0) * hG

end Ext218

end CFSG.CGT.Stroth77
