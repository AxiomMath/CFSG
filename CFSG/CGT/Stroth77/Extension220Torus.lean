module

public import CFSG.CGT.Stroth77.Extension218Images
public import CFSG.CGT.Stroth77.Extension24
public import CFSG.CGT.Stroth77.TorusNormalForm

public section

namespace CFSG.CGT.Stroth77

namespace Ext220

open Matrix Ext218

variable {s : ℕ} {i F G G' N K J : ℤ}

local macro "simp_t131" : tactic =>
  `(tactic| simp only [Type131.action, SigmaFourAction.ofMatEq, Type131.k, Type131.uvM,
    Type131.tM, Type131.uvA, Type131.ρM, Type131.uM, uMat, ofCols_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul])

local macro "simp_t230" : tactic =>
  `(tactic| simp only [Type230.action, SigmaFourAction.ofMatEq, Type230.k, Type230.uvM,
    Type230.tM, Type230.uvA, Type230.ρM, Type230.uM, uMat, ofCols_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul])

local macro "simp_t231" : tactic =>
  `(tactic| simp only [Type231.action, SigmaFourAction.ofMatEq, Type231.k, Type230.k,
    Type231.uvM, Type231.tM, Type231.uvA, Type231.ρM, Type231.uM, uMat, ofCols_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul])

theorem two_gen_one_eq220 {k : Fin 3 → ℕ} :
    (2 : ℤ) • gen k 1 = (0 : ℤ) • gen k 0 + (2 : ℤ) • gen k 1 + (0 : ℤ) • gen k 2 := by
  simp

theorem two_gen_two_eq220 {k : Fin 3 → ℕ} :
    (2 : ℤ) • gen k 2 = (0 : ℤ) • gen k 0 + (0 : ℤ) • gen k 1 + (2 : ℤ) • gen k 2 := by
  simp

theorem phiUV_gen0_t131 (h : Type131.Data (s + 2) i F G N K J) :
    (Type131.action h).φuv (gen (Type131.k (s + 2)) 0) =
      (-8 * G - 19 : ℤ) • gen (Type131.k (s + 2)) 0 +
        (4 * (2 : ℤ) ^ s + 2 : ℤ) • gen (Type131.k (s + 2)) 1 +
        (-2 : ℤ) • gen (Type131.k (s + 2)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 2 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
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

theorem phiUV_gen1_t131 (h : Type131.Data (s + 2) i F G N K J) :
    (Type131.action h).φuv (gen (Type131.k (s + 2)) 1) =
      (64 * G ^ 2 + 296 * G + 342 : ℤ) • gen (Type131.k (s + 2)) 0 +
        (-40 * G - 95 : ℤ) • gen (Type131.k (s + 2)) 1 +
        (16 * G + 4 * (2 : ℤ) ^ s + 38 : ℤ) • gen (Type131.k (s + 2)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 2 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
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

theorem phiUV_gen2_t131 (h : Type131.Data (s + 2) i F G N K J) :
    (Type131.action h).φuv (gen (Type131.k (s + 2)) 2) =
      (-768 * G ^ 3 - 256 * G ^ 2 * (2 : ℤ) ^ s - 6592 * G ^ 2 - 864 * G * (2 : ℤ) ^ s - 18284 * G -
          608 * (2 : ℤ) ^ s - 16530 : ℤ) • gen (Type131.k (s + 2)) 0 +
        (-256 * G ^ 2 * (2 : ℤ) ^ s - 1920 * G ^ 2 - 896 * G * (2 : ℤ) ^ s +
            16 * ((2 : ℤ) ^ s) ^ 2 - 9088 * G - 684 * (2 : ℤ) ^ s -
            10754 : ℤ) • gen (Type131.k (s + 2)) 1 +
        (-256 * G ^ 2 * (2 : ℤ) ^ s + 192 * G ^ 2 - 1184 * G * (2 : ℤ) ^ s + 928 * G -
            1368 * (2 : ℤ) ^ s + 1121 : ℤ) • gen (Type131.k (s + 2)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 2 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
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

theorem phiT_gen0_t131 (h : Type131.Data (s + 2) i F G N K J) :
    (Type131.action h).φt (gen (Type131.k (s + 2)) 0) =
      (-8 * G - 15 : ℤ) • gen (Type131.k (s + 2)) 0 + (2 : ℤ) • gen (Type131.k (s + 2)) 1 +
        (4 * (2 : ℤ) ^ s + 4 : ℤ) • gen (Type131.k (s + 2)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 2 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
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

theorem phiT_gen1_t131 (h : Type131.Data (s + 2) i F G N K J) :
    (Type131.action h).φt (gen (Type131.k (s + 2)) 1) =
      (32 * G ^ 2 + 76 * G : ℤ) • gen (Type131.k (s + 2)) 0 +
        (-56 * G + 4 * (2 : ℤ) ^ s - 133 : ℤ) • gen (Type131.k (s + 2)) 1 +
        (-64 * G - 152 : ℤ) • gen (Type131.k (s + 2)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 2 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
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

theorem phiT_gen2_t131 (h : Type131.Data (s + 2) i F G N K J) :
    (Type131.action h).φt (gen (Type131.k (s + 2)) 2) =
      (64 * G ^ 2 + 264 * G - 8 * (2 : ℤ) ^ s + 266 : ℤ) • gen (Type131.k (s + 2)) 0 +
        (-16 * G - 4 * (2 : ℤ) ^ s - 38 : ℤ) • gen (Type131.k (s + 2)) 1 +
        (-56 * G - 4 * (2 : ℤ) ^ s - 133 : ℤ) • gen (Type131.k (s + 2)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 2 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
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

theorem phiU_gen0_t131 (h : Type131.Data (s + 2) i F G N K J) :
    (Type131.action h).φu (gen (Type131.k (s + 2)) 0) =
      (2 * (2 : ℤ) ^ s - 1 : ℤ) • gen (Type131.k (s + 2)) 0 + (0 : ℤ) • gen (Type131.k (s + 2)) 1 +
        (0 : ℤ) • gen (Type131.k (s + 2)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 2 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
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

theorem phiU_gen1_t131 (h : Type131.Data (s + 2) i F G N K J) :
    (Type131.action h).φu (gen (Type131.k (s + 2)) 1) =
      (-16 * G - 36 : ℤ) • gen (Type131.k (s + 2)) 0 + (0 : ℤ) • gen (Type131.k (s + 2)) 1 +
        (1 : ℤ) • gen (Type131.k (s + 2)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 2 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
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

theorem phiU_gen2_t131 (h : Type131.Data (s + 2) i F G N K J) :
    (Type131.action h).φu (gen (Type131.k (s + 2)) 2) =
      (32 * G * (2 : ℤ) ^ s - 16 * G + 72 * (2 : ℤ) ^ s - 36 : ℤ) • gen (Type131.k (s + 2)) 0 +
        (1 : ℤ) • gen (Type131.k (s + 2)) 1 + (0 : ℤ) • gen (Type131.k (s + 2)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 2 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
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

theorem phiR_gen0_t131 (h : Type131.Data (s + 2) i F G N K J) :
    (Type131.action h).φρ (gen (Type131.k (s + 2)) 0) =
      (1 : ℤ) • gen (Type131.k (s + 2)) 0 + (0 : ℤ) • gen (Type131.k (s + 2)) 1 +
        (0 : ℤ) • gen (Type131.k (s + 2)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 2 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
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

theorem phiR_gen1_t131 (h : Type131.Data (s + 2) i F G N K J) :
    (Type131.action h).φρ (gen (Type131.k (s + 2)) 1) =
      (0 : ℤ) • gen (Type131.k (s + 2)) 0 + (0 : ℤ) • gen (Type131.k (s + 2)) 1 +
        (1 : ℤ) • gen (Type131.k (s + 2)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 2 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
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

theorem phiR_gen2_t131 (h : Type131.Data (s + 2) i F G N K J) :
    (Type131.action h).φρ (gen (Type131.k (s + 2)) 2) =
      (-2 : ℤ) • gen (Type131.k (s + 2)) 0 + (-1 : ℤ) • gen (Type131.k (s + 2)) 1 +
        (-1 : ℤ) • gen (Type131.k (s + 2)) 2 := by
  obtain ⟨hi, hF, hN, hK, -, hG⟩ := h
  subst hi hF hN
  obtain rfl : K = 2 * 2 ^ s := by rw [pow_add] at hK; norm_num at hK; linarith
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

theorem phiUV_gen0_t230_t131 (h : Type230.Data s i F G') (hGG : G' = 4 * G + 7)
    (hG : 3 * G + 7 = 16 * ((2 : ℤ) ^ s) ^ 2) :
    (Type230.action h).φuv (gen (Type230.k s) 0) =
      (-8 * G - 19 : ℤ) • gen (Type230.k s) 0 +
        (2 * (4 * (2 : ℤ) ^ s + 2) : ℤ) • gen (Type230.k s) 1 +
        (2 * (-2) : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, -, -⟩ := h
  subst hi hF hGG
  conv_lhs => rw [gen_zero_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (-32 * (2 : ℤ) ^ s : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (-8) * hG
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG

theorem phiUV_gen1_t230_t131 (h : Type230.Data s i F G') (hGG : G' = 4 * G + 7)
    (hG : 3 * G + 7 = 16 * ((2 : ℤ) ^ s) ^ 2) :
    (2 : ℤ) • (Type230.action h).φuv (gen (Type230.k s) 1) =
      (64 * G ^ 2 + 296 * G + 342 : ℤ) • gen (Type230.k s) 0 +
        (2 * (-40 * G - 95) : ℤ) • gen (Type230.k s) 1 +
        (2 * (16 * G + 4 * (2 : ℤ) ^ s + 38) : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, -, -⟩ := h
  subst hi hF hGG
  rw [← map_zsmul, two_gen_one_eq220]
  refine matAct_gens_eq _ _ 1 0 0
    (t0 := (20480 * ((2 : ℤ) ^ s) ^ 3 - 32 * (2 : ℤ) ^ s + 3 : ℤ))
    (t1 := (-80 * (2 : ℤ) ^ s + 1 : ℤ))
    (t2 := (32 * (2 : ℤ) ^ s - 1 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (5120 * ((2 : ℤ) ^ s) ^ 2 + 960 * G + 2232) * hG
  · simp_t230
    linear_combination (-80) * hG
  · simp_t230
    linear_combination (32) * hG

theorem phiUV_gen2_t230_t131 (h : Type230.Data s i F G') (hGG : G' = 4 * G + 7)
    (hG : 3 * G + 7 = 16 * ((2 : ℤ) ^ s) ^ 2) :
    (2 : ℤ) • (Type230.action h).φuv (gen (Type230.k s) 2) =
      (-768 * G ^ 3 - 256 * G ^ 2 * (2 : ℤ) ^ s - 6592 * G ^ 2 - 864 * G * (2 : ℤ) ^ s - 18284 * G -
          608 * (2 : ℤ) ^ s - 16530 : ℤ) • gen (Type230.k s) 0 +
        (2 * (-256 * G ^ 2 * (2 : ℤ) ^ s - 1920 * G ^ 2 - 896 * G * (2 : ℤ) ^ s +
            16 * ((2 : ℤ) ^ s) ^ 2 - 9088 * G - 684 * (2 : ℤ) ^ s -
            10754) : ℤ) • gen (Type230.k s) 1 +
        (2 * (-256 * G ^ 2 * (2 : ℤ) ^ s + 192 * G ^ 2 - 1184 * G * (2 : ℤ) ^ s + 928 * G -
            1368 * (2 : ℤ) ^ s + 1121) : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, -, -⟩ := h
  subst hi hF hGG
  rw [← map_zsmul, two_gen_two_eq220]
  refine matAct_gens_eq _ _ 2 1 1
    (t0 := (-16515072 * ((2 : ℤ) ^ s) ^ 5 - 507904 * ((2 : ℤ) ^ s) ^ 4 -
      1167360 * ((2 : ℤ) ^ s) ^ 3 + 15488 * ((2 : ℤ) ^ s) ^ 2 - 2532 * (2 : ℤ) ^ s - 28 : ℤ))
    (t1 := (-40960 * ((2 : ℤ) ^ s) ^ 4 - 307200 * ((2 : ℤ) ^ s) ^ 3 + 2816 * ((2 : ℤ) ^ s) ^ 2 -
      786 * (2 : ℤ) ^ s - 4 : ℤ))
    (t2 := (-40960 * ((2 : ℤ) ^ s) ^ 4 + 30720 * ((2 : ℤ) ^ s) ^ 3 + 2112 * ((2 : ℤ) ^ s) ^ 2 +
      162 * (2 : ℤ) ^ s + 1 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (-4128768 * ((2 : ℤ) ^ s) ^ 4 - 774144 * G * ((2 : ℤ) ^ s) ^ 2 -
      126976 * ((2 : ℤ) ^ s) ^ 3 - 145152 * G ^ 2 - 23808 * G * (2 : ℤ) ^ s -
      2098176 * ((2 : ℤ) ^ s) ^ 2 - 732096 * G - 51680 * (2 : ℤ) ^ s - 918540) * hG
  · simp_t230
    linear_combination (-40960 * ((2 : ℤ) ^ s) ^ 3 - 7680 * G * (2 : ℤ) ^ s -
      307200 * ((2 : ℤ) ^ s) ^ 2 - 57600 * G - 15104 * (2 : ℤ) ^ s - 135168) * hG
  · simp_t230
    linear_combination (-40960 * ((2 : ℤ) ^ s) ^ 3 - 7680 * G * (2 : ℤ) ^ s +
      30720 * ((2 : ℤ) ^ s) ^ 2 + 5760 * G - 15808 * (2 : ℤ) ^ s + 13632) * hG

theorem phiT_gen0_t230_t131 (h : Type230.Data s i F G') (hGG : G' = 4 * G + 7)
    (hG : 3 * G + 7 = 16 * ((2 : ℤ) ^ s) ^ 2) :
    (Type230.action h).φt (gen (Type230.k s) 0) =
      (-8 * G - 15 : ℤ) • gen (Type230.k s) 0 + (2 * (2) : ℤ) • gen (Type230.k s) 1 +
        (2 * (4 * (2 : ℤ) ^ s + 4) : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, -, -⟩ := h
  subst hi hF hGG
  conv_lhs => rw [gen_zero_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (-32 * (2 : ℤ) ^ s : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (-8) * hG
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG

theorem phiT_gen1_t230_t131 (h : Type230.Data s i F G') (hGG : G' = 4 * G + 7)
    (hG : 3 * G + 7 = 16 * ((2 : ℤ) ^ s) ^ 2) :
    (2 : ℤ) • (Type230.action h).φt (gen (Type230.k s) 1) =
      (32 * G ^ 2 + 76 * G : ℤ) • gen (Type230.k s) 0 +
        (2 * (-56 * G + 4 * (2 : ℤ) ^ s - 133) : ℤ) • gen (Type230.k s) 1 +
        (2 * (-64 * G - 152) : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, -, -⟩ := h
  subst hi hF hGG
  rw [← map_zsmul, two_gen_one_eq220]
  refine matAct_gens_eq _ _ 1 0 0
    (t0 := (10240 * ((2 : ℤ) ^ s) ^ 3 - 880 * (2 : ℤ) ^ s + 3 : ℤ))
    (t1 := (-112 * (2 : ℤ) ^ s - 1 : ℤ))
    (t2 := (-128 * (2 : ℤ) ^ s + 1 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (2560 * ((2 : ℤ) ^ s) ^ 2 + 480 * G + 900) * hG
  · simp_t230
    linear_combination (-112) * hG
  · simp_t230
    linear_combination (-128) * hG

theorem phiT_gen2_t230_t131 (h : Type230.Data s i F G') (hGG : G' = 4 * G + 7)
    (hG : 3 * G + 7 = 16 * ((2 : ℤ) ^ s) ^ 2) :
    (2 : ℤ) • (Type230.action h).φt (gen (Type230.k s) 2) =
      (64 * G ^ 2 + 264 * G - 8 * (2 : ℤ) ^ s + 266 : ℤ) • gen (Type230.k s) 0 +
        (2 * (-16 * G - 4 * (2 : ℤ) ^ s - 38) : ℤ) • gen (Type230.k s) 1 +
        (2 * (-56 * G - 4 * (2 : ℤ) ^ s - 133) : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, -, -⟩ := h
  subst hi hF hGG
  rw [← map_zsmul, two_gen_two_eq220]
  refine matAct_gens_eq _ _ 1 0 0
    (t0 := (20480 * ((2 : ℤ) ^ s) ^ 3 - 416 * (2 : ℤ) ^ s + 15 : ℤ))
    (t1 := (-32 * (2 : ℤ) ^ s + 1 : ℤ))
    (t2 := (-112 * (2 : ℤ) ^ s + 2 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (5120 * ((2 : ℤ) ^ s) ^ 2 + 960 * G + 2136) * hG
  · simp_t230
    linear_combination (-32) * hG
  · simp_t230
    linear_combination (-112) * hG

theorem phiU_gen0_t230_t131 (h : Type230.Data s i F G') (hGG : G' = 4 * G + 7)
    (hG : 3 * G + 7 = 16 * ((2 : ℤ) ^ s) ^ 2) :
    (Type230.action h).φu (gen (Type230.k s) 0) =
      (2 * (2 : ℤ) ^ s - 1 : ℤ) • gen (Type230.k s) 0 + (2 * (0) : ℤ) • gen (Type230.k s) 1 +
        (2 * (0) : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, -, -⟩ := h
  subst hi hF hGG
  conv_lhs => rw [gen_zero_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG

theorem phiU_gen1_t230_t131 (h : Type230.Data s i F G') (hGG : G' = 4 * G + 7)
    (hG : 3 * G + 7 = 16 * ((2 : ℤ) ^ s) ^ 2) :
    (2 : ℤ) • (Type230.action h).φu (gen (Type230.k s) 1) =
      (-16 * G - 36 : ℤ) • gen (Type230.k s) 0 + (2 * (0) : ℤ) • gen (Type230.k s) 1 +
        (2 * (1) : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, -, -⟩ := h
  subst hi hF hGG
  rw [← map_zsmul, two_gen_one_eq220]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (-64 * (2 : ℤ) ^ s + 1 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (-16) * hG
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG

theorem phiU_gen2_t230_t131 (h : Type230.Data s i F G') (hGG : G' = 4 * G + 7)
    (hG : 3 * G + 7 = 16 * ((2 : ℤ) ^ s) ^ 2) :
    (2 : ℤ) • (Type230.action h).φu (gen (Type230.k s) 2) =
      (32 * G * (2 : ℤ) ^ s - 16 * G + 72 * (2 : ℤ) ^ s - 36 : ℤ) • gen (Type230.k s) 0 +
        (2 * (1) : ℤ) • gen (Type230.k s) 1 + (2 * (0) : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, -, -⟩ := h
  subst hi hF hGG
  rw [← map_zsmul, two_gen_two_eq220]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (128 * ((2 : ℤ) ^ s) ^ 2 - 66 * (2 : ℤ) ^ s + 1 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (32 * (2 : ℤ) ^ s - 16) * hG
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG

theorem phiR_gen0_t230_t131 (h : Type230.Data s i F G') (hGG : G' = 4 * G + 7)
    (hG : 3 * G + 7 = 16 * ((2 : ℤ) ^ s) ^ 2) :
    (Type230.action h).φρ (gen (Type230.k s) 0) =
      (1 : ℤ) • gen (Type230.k s) 0 + (2 * (0) : ℤ) • gen (Type230.k s) 1 +
        (2 * (0) : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, -, -⟩ := h
  subst hi hF hGG
  conv_lhs => rw [gen_zero_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG

theorem phiR_gen1_t230_t131 (h : Type230.Data s i F G') (hGG : G' = 4 * G + 7)
    (hG : 3 * G + 7 = 16 * ((2 : ℤ) ^ s) ^ 2) :
    (2 : ℤ) • (Type230.action h).φρ (gen (Type230.k s) 1) =
      (0 : ℤ) • gen (Type230.k s) 0 + (2 * (0) : ℤ) • gen (Type230.k s) 1 +
        (2 * (1) : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, -, -⟩ := h
  subst hi hF hGG
  rw [← map_zsmul, two_gen_one_eq220]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG

theorem phiR_gen2_t230_t131 (h : Type230.Data s i F G') (hGG : G' = 4 * G + 7)
    (hG : 3 * G + 7 = 16 * ((2 : ℤ) ^ s) ^ 2) :
    (2 : ℤ) • (Type230.action h).φρ (gen (Type230.k s) 2) =
      (-2 : ℤ) • gen (Type230.k s) 0 + (2 * (-1) : ℤ) • gen (Type230.k s) 1 +
        (2 * (-1) : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, -, -⟩ := h
  subst hi hF hGG
  rw [← map_zsmul, two_gen_two_eq220]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG

theorem phiUV_c1_t230 (h : Type230.Data s i F G) :
    (Type230.action h).φuv
        ((2 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 0 + (0 : ℤ) • gen (Type230.k s) 1 +
          (0 : ℤ) • gen (Type230.k s) 2) =
      (2 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 0 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 1 +
        (8 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 1 0 0
    (t0 := (-256 * ((2 : ℤ) ^ s) ^ 2 - 2 : ℤ))
    (t1 := ((2 : ℤ) ^ s : ℤ))
    (t2 := (-1 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (-16 * (2 : ℤ) ^ s) * hG
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG

theorem phiUV_a1_t230 (h : Type230.Data s i F G) :
    (Type230.action h).φuv
        ((0 : ℤ) • gen (Type230.k s) 0 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 1 +
          (0 : ℤ) • gen (Type230.k s) 2) =
      (0 : ℤ) • gen (Type230.k s) 0 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 1 +
        (0 : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 2 1 1
    (t0 := (262144 * ((2 : ℤ) ^ s) ^ 4 - 512 * ((2 : ℤ) ^ s) ^ 2 + 36 * (2 : ℤ) ^ s - 2 : ℤ))
    (t1 := (-1280 * ((2 : ℤ) ^ s) ^ 2 + 12 * (2 : ℤ) ^ s - 4 : ℤ))
    (t2 := (512 * ((2 : ℤ) ^ s) ^ 2 - 6 * (2 : ℤ) ^ s + 1 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (16384 * ((2 : ℤ) ^ s) ^ 3 + 768 * G * (2 : ℤ) ^ s +
      1760 * (2 : ℤ) ^ s) * hG
  · simp_t230
    linear_combination (-320 * (2 : ℤ) ^ s) * hG
  · simp_t230
    linear_combination (128 * (2 : ℤ) ^ s) * hG

theorem phiUV_b1_t230 (h : Type230.Data s i F G) :
    (Type230.action h).φuv
        ((0 : ℤ) • gen (Type230.k s) 0 + (0 : ℤ) • gen (Type230.k s) 1 +
          (8 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 2) =
      (0 : ℤ) • gen (Type230.k s) 0 + (0 : ℤ) • gen (Type230.k s) 1 +
        (8 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 2 2 2
    (t0 := (-67108864 * ((2 : ℤ) ^ s) ^ 6 - 2097152 * ((2 : ℤ) ^ s) ^ 5 -
      4980736 * ((2 : ℤ) ^ s) ^ 4 + 77824 * ((2 : ℤ) ^ s) ^ 3 - 13264 * ((2 : ℤ) ^ s) ^ 2 +
      16 * (2 : ℤ) ^ s - 6 : ℤ))
    (t1 := (-524288 * ((2 : ℤ) ^ s) ^ 5 - 3932160 * ((2 : ℤ) ^ s) ^ 4 + 40960 * ((2 : ℤ) ^ s) ^ 3 -
      12432 * ((2 : ℤ) ^ s) ^ 2 + 10 * (2 : ℤ) ^ s - 9 : ℤ))
    (t2 := (-524288 * ((2 : ℤ) ^ s) ^ 5 + 393216 * ((2 : ℤ) ^ s) ^ 4 + 25600 * ((2 : ℤ) ^ s) ^ 3 +
      2712 * ((2 : ℤ) ^ s) ^ 2 + 16 * (2 : ℤ) ^ s : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (-4194304 * ((2 : ℤ) ^ s) ^ 5 - 196608 * G * ((2 : ℤ) ^ s) ^ 3 -
      131072 * ((2 : ℤ) ^ s) ^ 4 - 9216 * G ^ 2 * (2 : ℤ) ^ s - 6144 * G * ((2 : ℤ) ^ s) ^ 2 -
      770048 * ((2 : ℤ) ^ s) ^ 3 - 57600 * G * (2 : ℤ) ^ s - 9472 * ((2 : ℤ) ^ s) ^ 2 -
      85008 * (2 : ℤ) ^ s) * hG
  · simp_t230
    linear_combination (-131072 * ((2 : ℤ) ^ s) ^ 4 - 6144 * G * ((2 : ℤ) ^ s) ^ 2 -
      983040 * ((2 : ℤ) ^ s) ^ 3 - 46080 * G * (2 : ℤ) ^ s - 4096 * ((2 : ℤ) ^ s) ^ 2 -
      110592 * (2 : ℤ) ^ s) * hG
  · simp_t230
    linear_combination (-131072 * ((2 : ℤ) ^ s) ^ 4 - 6144 * G * ((2 : ℤ) ^ s) ^ 2 +
      98304 * ((2 : ℤ) ^ s) ^ 3 + 4608 * G * (2 : ℤ) ^ s - 7936 * ((2 : ℤ) ^ s) ^ 2 +
      11520 * (2 : ℤ) ^ s) * hG

theorem phiU_c1_t230 (h : Type230.Data s i F G) :
    (Type230.action h).φu
        ((2 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 0 + (0 : ℤ) • gen (Type230.k s) 1 +
          (0 : ℤ) • gen (Type230.k s) 2) =
      (2 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 0 + (0 : ℤ) • gen (Type230.k s) 1 +
        (0 : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := ((2 : ℤ) ^ s - 1 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG

theorem phiU_a1_t230 (h : Type230.Data s i F G) :
    (Type230.action h).φu
        ((0 : ℤ) • gen (Type230.k s) 0 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 1 +
          (0 : ℤ) • gen (Type230.k s) 2) =
      (0 : ℤ) • gen (Type230.k s) 0 + (0 : ℤ) • gen (Type230.k s) 1 +
        (8 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 1 0 0
    (t0 := (-1024 * ((2 : ℤ) ^ s) ^ 2 + 12 * (2 : ℤ) ^ s + 4 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (-64 * (2 : ℤ) ^ s) * hG
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG

theorem phiU_b1_t230 (h : Type230.Data s i F G) :
    (Type230.action h).φu
        ((0 : ℤ) • gen (Type230.k s) 0 + (0 : ℤ) • gen (Type230.k s) 1 +
          (8 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 2) =
      (0 : ℤ) • gen (Type230.k s) 0 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 1 +
        (0 : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 1 0 0
    (t0 := (2048 * ((2 : ℤ) ^ s) ^ 3 - 1048 * ((2 : ℤ) ^ s) ^ 2 + 4 * (2 : ℤ) ^ s + 4 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (128 * ((2 : ℤ) ^ s) ^ 2 - 64 * (2 : ℤ) ^ s) * hG
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG

theorem phiR_c1_t230 (h : Type230.Data s i F G) :
    (Type230.action h).φρ
        ((2 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 0 + (0 : ℤ) • gen (Type230.k s) 1 +
          (0 : ℤ) • gen (Type230.k s) 2) =
      (2 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 0 + (0 : ℤ) • gen (Type230.k s) 1 +
        (0 : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG

theorem phiR_a1_t230 (h : Type230.Data s i F G) :
    (Type230.action h).φρ
        ((0 : ℤ) • gen (Type230.k s) 0 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 1 +
          (0 : ℤ) • gen (Type230.k s) 2) =
      (0 : ℤ) • gen (Type230.k s) 0 + (0 : ℤ) • gen (Type230.k s) 1 +
        (8 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG

theorem phiR_b1_t230 (h : Type230.Data s i F G) :
    (Type230.action h).φρ
        ((0 : ℤ) • gen (Type230.k s) 0 + (0 : ℤ) • gen (Type230.k s) 1 +
          (8 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 2) =
      (0 : ℤ) • gen (Type230.k s) 0 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 1 +
        (8 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (-2 : ℤ))
    (t1 := (-1 : ℤ))
    (t2 := (-1 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG

@[expose] def tor230 (s : ℕ) (x y z : ℤ) : Torus (Type230.k s) :=
  (x * 2 ^ (s + 1)) • gen (Type230.k s) 0 + (y * 2 ^ (s + 3)) • gen (Type230.k s) 1 +
    (z * 2 ^ (s + 3)) • gen (Type230.k s) 2

theorem tor230_eq_iff {x y z x' y' z' : ℤ} :
    tor230 s x y z = tor230 s x' y' z' ↔ 2 ∣ x' - x ∧ 2 ∣ y' - y ∧ 2 ∣ z' - z := by
  have hs1 : (2 : ℤ) ^ (s + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hs3 : (2 : ℤ) ^ (s + 3) ≠ 0 := pow_ne_zero _ two_ne_zero
  have e0 : x' * 2 ^ (s + 1) - x * 2 ^ (s + 1) = 2 ^ (s + 1) * (x' - x) := by ring
  have e1 : y' * 2 ^ (s + 3) - y * 2 ^ (s + 3) = 2 ^ (s + 3) * (y' - y) := by ring
  have e2 : z' * 2 ^ (s + 3) - z * 2 ^ (s + 3) = 2 ^ (s + 3) * (z' - z) := by ring
  constructor
  · intro h
    obtain ⟨h0, h1, h2⟩ := zsmul_gens_dvd_of_eq h
    change (2 : ℤ) ^ (s + 2) ∣ _ at h0
    change (2 : ℤ) ^ (s + 4) ∣ _ at h1
    change (2 : ℤ) ^ (s + 4) ∣ _ at h2
    rw [e0, show s + 2 = (s + 1) + 1 by ring, pow_succ] at h0
    rw [e1, show s + 4 = (s + 3) + 1 by ring, pow_succ] at h1
    rw [e2, show s + 4 = (s + 3) + 1 by ring, pow_succ] at h2
    exact ⟨(mul_dvd_mul_iff_left hs1).mp h0, (mul_dvd_mul_iff_left hs3).mp h1,
      (mul_dvd_mul_iff_left hs3).mp h2⟩
  · rintro ⟨h0, h1, h2⟩
    apply zsmul_gens_eq_of_dvd
    · change (2 : ℤ) ^ (s + 2) ∣ _
      rw [e0, show s + 2 = (s + 1) + 1 by ring, pow_succ]
      exact mul_dvd_mul_left _ h0
    · change (2 : ℤ) ^ (s + 4) ∣ _
      rw [e1, show s + 4 = (s + 3) + 1 by ring, pow_succ]
      exact mul_dvd_mul_left _ h1
    · change (2 : ℤ) ^ (s + 4) ∣ _
      rw [e2, show s + 4 = (s + 3) + 1 by ring, pow_succ]
      exact mul_dvd_mul_left _ h2

theorem tor230_congr {x y z x' y' z' : ℤ} (h0 : 2 ∣ x' - x) (h1 : 2 ∣ y' - y)
    (h2 : 2 ∣ z' - z) : tor230 s x y z = tor230 s x' y' z' :=
  tor230_eq_iff.mpr ⟨h0, h1, h2⟩

theorem tor230_zero : tor230 s 0 0 0 = 0 := by
  simp [tor230]

theorem tor230_add (x y z x' y' z' : ℤ) :
    tor230 s x y z + tor230 s x' y' z' = tor230 s (x + x') (y + y') (z + z') := by
  simp only [tor230]
  module

theorem zsmul_tor230 (n x y z : ℤ) : n • tor230 s x y z = tor230 s (n * x) (n * y) (n * z) := by
  simp only [tor230]
  module

theorem neg_tor230 (x y z : ℤ) : -tor230 s x y z = tor230 s (-x) (-y) (-z) := by
  simp only [tor230]
  module

theorem two_zsmul_tor230 (x y z : ℤ) : (2 : ℤ) • tor230 s x y z = 0 := by
  rw [zsmul_tor230, ← tor230_zero]
  exact tor230_congr ⟨-x, by ring⟩ ⟨-y, by ring⟩ ⟨-z, by ring⟩

theorem even_zsmul_tor230 (Q x y z : ℤ) : (2 * Q) • tor230 s x y z = 0 := by
  rw [mul_comm, mul_zsmul, two_zsmul_tor230, smul_zero]

theorem odd_zsmul_tor230 (Q x y z : ℤ) : (2 * Q + 1) • tor230 s x y z = tor230 s x y z := by
  rw [add_zsmul, even_zsmul_tor230, one_zsmul, zero_add]

theorem exists_tor230 {w : Torus (Type230.k s)} (hw : (2 : ℤ) • w = 0) :
    ∃ x y z : ℤ, w = tor230 s x y z := by
  obtain ⟨p, q, r, rfl⟩ := torus_eq_zsmul_gens (Type230.k s) w
  have h : (2 * p) • gen (Type230.k s) 0 + (2 * q) • gen (Type230.k s) 1 +
      (2 * r) • gen (Type230.k s) 2 = (0 : ℤ) • gen (Type230.k s) 0 +
      (0 : ℤ) • gen (Type230.k s) 1 + (0 : ℤ) • gen (Type230.k s) 2 := by
    rw [zero_smul, zero_smul, zero_smul, add_zero, add_zero, ← hw]
    module
  obtain ⟨h0, h1, h2⟩ := zsmul_gens_dvd_of_eq h
  change (2 : ℤ) ^ (s + 2) ∣ _ at h0
  change (2 : ℤ) ^ (s + 4) ∣ _ at h1
  change (2 : ℤ) ^ (s + 4) ∣ _ at h2
  have two_ne : (2 : ℤ) ≠ 0 := two_ne_zero
  rw [show (0 : ℤ) - 2 * p = 2 * (-p) by ring, show s + 2 = (s + 1) + 1 by ring, pow_succ,
    mul_comm _ (2 : ℤ)] at h0
  rw [show (0 : ℤ) - 2 * q = 2 * (-q) by ring, show s + 4 = (s + 3) + 1 by ring, pow_succ,
    mul_comm _ (2 : ℤ)] at h1
  rw [show (0 : ℤ) - 2 * r = 2 * (-r) by ring, show s + 4 = (s + 3) + 1 by ring, pow_succ,
    mul_comm _ (2 : ℤ)] at h2
  obtain ⟨x, hx⟩ := dvd_neg.mp ((mul_dvd_mul_iff_left two_ne).mp h0)
  obtain ⟨y, hy⟩ := dvd_neg.mp ((mul_dvd_mul_iff_left two_ne).mp h1)
  obtain ⟨z, hz⟩ := dvd_neg.mp ((mul_dvd_mul_iff_left two_ne).mp h2)
  refine ⟨x, y, z, ?_⟩
  rw [hx, hy, hz]
  simp only [tor230]
  module

theorem tor230_eq_smul (x y z : ℤ) : tor230 s x y z =
    x • ((2 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 0 + (0 : ℤ) • gen (Type230.k s) 1 +
      (0 : ℤ) • gen (Type230.k s) 2) +
    y • ((0 : ℤ) • gen (Type230.k s) 0 + (8 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 1 +
      (0 : ℤ) • gen (Type230.k s) 2) +
    z • ((0 : ℤ) • gen (Type230.k s) 0 + (0 : ℤ) • gen (Type230.k s) 1 +
      (8 * (2 : ℤ) ^ s : ℤ) • gen (Type230.k s) 2) := by
  simp only [tor230, pow_succ]
  module

theorem phiUV_tor230 (h : Type230.Data s i F G) (x y z : ℤ) :
    (Type230.action h).φuv (tor230 s x y z) = tor230 s x (x + y) (x + z) := by
  rw [tor230_eq_smul, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, phiUV_c1_t230 h,
    phiUV_a1_t230 h, phiUV_b1_t230 h]
  simp only [tor230, pow_succ]
  module

theorem phiU_tor230 (h : Type230.Data s i F G) (x y z : ℤ) :
    (Type230.action h).φu (tor230 s x y z) = tor230 s x z y := by
  rw [tor230_eq_smul, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, phiU_c1_t230 h,
    phiU_a1_t230 h, phiU_b1_t230 h]
  simp only [tor230, pow_succ]
  module

theorem phiR_tor230 (h : Type230.Data s i F G) (x y z : ℤ) :
    (Type230.action h).φρ (tor230 s x y z) = tor230 s x z (y + z) := by
  rw [tor230_eq_smul, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, phiR_c1_t230 h,
    phiR_a1_t230 h, phiR_b1_t230 h]
  simp only [tor230, pow_succ]
  module

theorem phiR_apply_gens_t230 (h : Type230.Data s i F G) (a b c : ℤ) :
    (Type230.action h).φρ
        (a • gen (Type230.k s) 0 + b • gen (Type230.k s) 1 + c • gen (Type230.k s) 2) =
      (a - c) • gen (Type230.k s) 0 + (-c) • gen (Type230.k s) 1 +
        (b - c) • gen (Type230.k s) 2 := by
  refine matAct_gens_eq _ _ 0 0 0 (t0 := 0) (t1 := 0) (t2 := 0) ?_ ?_ ?_ <;>
  · simp_t230
    ring

theorem phiR_gen1_t230 (h : Type230.Data s i F G) :
    (Type230.action h).φρ (gen (Type230.k s) 1) = gen (Type230.k s) 2 := by
  conv_lhs => rw [gen_one_eq218]
  rw [phiR_apply_gens_t230 h]
  simp

theorem phiR_gen2_t230 (h : Type230.Data s i F G) :
    (Type230.action h).φρ (gen (Type230.k s) 2) =
      (-1 : ℤ) • gen (Type230.k s) 0 + (-1 : ℤ) • gen (Type230.k s) 1 +
        (-1 : ℤ) • gen (Type230.k s) 2 := by
  conv_lhs => rw [gen_two_eq218]
  rw [phiR_apply_gens_t230 h]
  simp


theorem uv_gen1_par_t230 (h : Type230.Data s i F G) :
    ∃ p Q R : ℤ, (Type230.action h).φuv (gen (Type230.k s) 1) = p • gen (Type230.k s) 0 +
      (2 * Q + 1) • gen (Type230.k s) 1 + (2 * R) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, -, -⟩ := h
  subst hi hF
  refine ⟨32 * G ^ 2 + 148 * G + 2 * (2 : ℤ) ^ s + 171,
    -20 * G + 4 * (2 : ℤ) ^ s - 48,
    8 * G - 2 * (2 : ℤ) ^ s + 19, ?_⟩
  conv_lhs => rw [gen_one_eq218]
  refine matAct_gens_eq _ _ 0 0 0 (t0 := 0) (t1 := 0) (t2 := 0) ?_ ?_ ?_ <;>
  · simp_t230
    ring

theorem uv_gen2_par_t230 (h : Type230.Data s i F G) :
    ∃ p Q R : ℤ, (Type230.action h).φuv (gen (Type230.k s) 2) = p • gen (Type230.k s) 0 +
      (2 * Q) • gen (Type230.k s) 1 + (2 * R + 1) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, -, -⟩ := h
  subst hi hF
  refine ⟨-384 * G ^ 3 - 256 * G ^ 2 * (2 : ℤ) ^ s - 3296 * G ^ 2 - 992 * G * (2 : ℤ) ^ s -
    40 * ((2 : ℤ) ^ s) ^ 2 - 9142 * G - 920 * (2 : ℤ) ^ s - 8265,
    -128 * G ^ 2 * (2 : ℤ) ^ s - 960 * G ^ 2 - 384 * G * (2 : ℤ) ^ s - 16 * ((2 : ℤ) ^ s) ^ 2 -
    4544 * G - 198 * (2 : ℤ) ^ s - 5377,
    -128 * G ^ 2 * (2 : ℤ) ^ s + 96 * G ^ 2 - 464 * G * (2 : ℤ) ^ s - 40 * ((2 : ℤ) ^ s) ^ 2 +
    464 * G - 384 * (2 : ℤ) ^ s + 560, ?_⟩
  conv_lhs => rw [gen_two_eq218]
  refine matAct_gens_eq _ _ 0 0 0 (t0 := 0) (t1 := 0) (t2 := 0) ?_ ?_ ?_ <;>
  · simp_t230
    ring

theorem u_gen1_par_t230 (h : Type230.Data s i F G) :
    ∃ p Q R : ℤ, (Type230.action h).φu (gen (Type230.k s) 1) = p • gen (Type230.k s) 0 +
      (2 * Q) • gen (Type230.k s) 1 + (2 * R + 1) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, -, -⟩ := h
  subst hi hF
  refine ⟨-8 * G + 2 * (2 : ℤ) ^ s - 18,
    0,
    0, ?_⟩
  conv_lhs => rw [gen_one_eq218]
  refine matAct_gens_eq _ _ 0 0 0 (t0 := 0) (t1 := 0) (t2 := 0) ?_ ?_ ?_ <;>
  · simp_t230
    ring

theorem u_gen2_par_t230 (h : Type230.Data s i F G) :
    ∃ p Q R : ℤ, (Type230.action h).φu (gen (Type230.k s) 2) = p • gen (Type230.k s) 0 +
      (2 * Q + 1) • gen (Type230.k s) 1 + (2 * R) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, -, -⟩ := h
  subst hi hF
  refine ⟨16 * G * (2 : ℤ) ^ s - 4 * ((2 : ℤ) ^ s) ^ 2 - 8 * G + 38 * (2 : ℤ) ^ s - 18,
    0,
    0, ?_⟩
  conv_lhs => rw [gen_two_eq218]
  refine matAct_gens_eq _ _ 0 0 0 (t0 := 0) (t1 := 0) (t2 := 0) ?_ ?_ ?_ <;>
  · simp_t230
    ring

theorem dev_apply220 {k : Fin 3 → ℕ} (X A : Torus k →+ Torus k) {ω₁ ω₂ : Torus k}
    (h0 : X (gen k 0) = A (gen k 0)) (h1 : X (gen k 1) = A (gen k 1) + ω₁)
    (h2 : X (gen k 2) = A (gen k 2) + ω₂) (p q r : ℤ) :
    X (p • gen k 0 + q • gen k 1 + r • gen k 2) =
      A (p • gen k 0 + q • gen k 1 + r • gen k 2) + q • ω₁ + r • ω₂ := by
  simp only [map_add, map_zsmul, h0, h1, h2, smul_add]
  abel

theorem dev_tor230 (X A : Torus (Type230.k s) →+ Torus (Type230.k s)) {x₁ y₁ z₁ x₂ y₂ z₂ : ℤ}
    (h0 : X (gen (Type230.k s) 0) = A (gen (Type230.k s) 0))
    (h1 : X (gen (Type230.k s) 1) = A (gen (Type230.k s) 1) + tor230 s x₁ y₁ z₁)
    (h2 : X (gen (Type230.k s) 2) = A (gen (Type230.k s) 2) + tor230 s x₂ y₂ z₂)
    (x y z : ℤ) : X (tor230 s x y z) = A (tor230 s x y z) := by
  have e : tor230 s x y z = (x * 2 ^ (s + 1)) • gen (Type230.k s) 0 +
      (y * 2 ^ (s + 3)) • gen (Type230.k s) 1 + (z * 2 ^ (s + 3)) • gen (Type230.k s) 2 := rfl
  rw [e, dev_apply220 X A h0 h1 h2, show y * 2 ^ (s + 3) = 2 * (y * 2 ^ (s + 2)) by ring,
    show z * 2 ^ (s + 3) = 2 * (z * 2 ^ (s + 2)) by ring, even_zsmul_tor230,
    even_zsmul_tor230, add_zero, add_zero]

@[expose] def act231 (h : Type231.Data s i F G) : SigmaFourAction (Type230.k s) :=
  Type231.action h

theorem phiUV_gen0_exact_t230 (h : Type230.Data s i F G) :
    (Type230.action h).φuv (gen (Type230.k s) 0) =
      (-8 * G - 19 : ℤ) • gen (Type230.k s) 0 + (8 * (2 : ℤ) ^ s + 4 : ℤ) • gen (Type230.k s) 1 +
        (-4 : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  conv_lhs => rw [gen_zero_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG

theorem phiUV_gen1_exact_t230 (h : Type230.Data s i F G) :
    (Type230.action h).φuv (gen (Type230.k s) 1) =
      (32 * G ^ 2 + 148 * G + 2 * (2 : ℤ) ^ s + 171 : ℤ) • gen (Type230.k s) 0 +
        (-40 * G + 8 * (2 : ℤ) ^ s - 95 : ℤ) • gen (Type230.k s) 1 +
        (16 * G - 4 * (2 : ℤ) ^ s + 38 : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  conv_lhs => rw [gen_one_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG

theorem phiUV_gen2_exact_t230 (h : Type230.Data s i F G) :
    (Type230.action h).φuv (gen (Type230.k s) 2) =
      (-384 * G ^ 3 - 256 * G ^ 2 * (2 : ℤ) ^ s - 3296 * G ^ 2 - 992 * G * (2 : ℤ) ^ s -
          40 * ((2 : ℤ) ^ s) ^ 2 - 9142 * G - 920 * (2 : ℤ) ^ s -
          8265 : ℤ) • gen (Type230.k s) 0 +
        (-256 * G ^ 2 * (2 : ℤ) ^ s - 1920 * G ^ 2 - 768 * G * (2 : ℤ) ^ s -
            32 * ((2 : ℤ) ^ s) ^ 2 - 9088 * G - 396 * (2 : ℤ) ^ s -
            10754 : ℤ) • gen (Type230.k s) 1 +
        (-256 * G ^ 2 * (2 : ℤ) ^ s + 192 * G ^ 2 - 928 * G * (2 : ℤ) ^ s - 80 * ((2 : ℤ) ^ s) ^ 2 +
            928 * G - 768 * (2 : ℤ) ^ s + 1121 : ℤ) • gen (Type230.k s) 2 := by
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  conv_lhs => rw [gen_two_eq218]
  refine matAct_gens_eq _ _ 0 0 0
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG
  · simp_t230
    linear_combination (0) * hG

theorem phiUV_gen0_t231_t230 (h : Type230.Data s i F G) (h' : Type231.Data s i F G) :
    (act231 h').φuv (gen (Type230.k s) 0) =
      (Type230.action h).φuv (gen (Type230.k s) 0) := by
  rw [phiUV_gen0_exact_t230 h]
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  change matAct (Type230.k s) (Type231.uvM s (8 * G + 19) (4 * G + 9) G) _
    (gen (Type230.k s) 0) = _
  conv_lhs => rw [gen_zero_eq218]
  refine (matAct_gens_eq _ _ 0 0 0
    (x' := (-8 * G - 19 : ℤ))
    (y' := (8 * (2 : ℤ) ^ s + 4 : ℤ))
    (z' := (-4 : ℤ))
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_).trans ?_
  · simp_t231
    linear_combination (0) * hG
  · simp_t231
    linear_combination (0) * hG
  · simp_t231
    linear_combination (0) * hG
  · rfl

theorem phiUV_gen1_t231_t230 (h : Type230.Data s i F G) (h' : Type231.Data s i F G) :
    (act231 h').φuv (gen (Type230.k s) 1) =
      (Type230.action h).φuv (gen (Type230.k s) 1) + tor230 s 0 0 1 := by
  rw [phiUV_gen1_exact_t230 h]
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  change matAct (Type230.k s) (Type231.uvM s (8 * G + 19) (4 * G + 9) G) _
    (gen (Type230.k s) 1) = _
  conv_lhs => rw [gen_one_eq218]
  refine (matAct_gens_eq _ _ 0 0 0
    (x' := (32 * G ^ 2 + 148 * G + 2 * (2 : ℤ) ^ s + 171 : ℤ))
    (y' := (-40 * G + 8 * (2 : ℤ) ^ s - 95 : ℤ))
    (z' := (16 * G + 4 * (2 : ℤ) ^ s + 38 : ℤ))
    (t0 := (0 : ℤ))
    (t1 := (0 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_).trans ?_
  · simp_t231
    linear_combination (0) * hG
  · simp_t231
    linear_combination (0) * hG
  · simp_t231
    linear_combination (0) * hG
  · simp only [tor230]
    module

theorem phiUV_gen2_t231_t230 (h : Type230.Data s i F G) (h' : Type231.Data s i F G) :
    (act231 h').φuv (gen (Type230.k s) 2) =
      (Type230.action h).φuv (gen (Type230.k s) 2) + tor230 s 0 1 0 := by
  rw [phiUV_gen2_exact_t230 h]
  obtain ⟨hi, hF, hG, -⟩ := h
  subst hi hF
  change matAct (Type230.k s) (Type231.uvM s (8 * G + 19) (4 * G + 9) G) _
    (gen (Type230.k s) 2) = _
  conv_lhs => rw [gen_two_eq218]
  refine (matAct_gens_eq _ _ 2 0 0
    (x' := (-384 * G ^ 3 - 256 * G ^ 2 * (2 : ℤ) ^ s - 3296 * G ^ 2 - 992 * G * (2 : ℤ) ^ s -
      40 * ((2 : ℤ) ^ s) ^ 2 - 9142 * G - 920 * (2 : ℤ) ^ s - 8265 : ℤ))
    (y' := (-256 * G ^ 2 * (2 : ℤ) ^ s - 1920 * G ^ 2 - 768 * G * (2 : ℤ) ^ s -
      32 * ((2 : ℤ) ^ s) ^ 2 - 9088 * G - 388 * (2 : ℤ) ^ s - 10754 : ℤ))
    (z' := (-256 * G ^ 2 * (2 : ℤ) ^ s + 192 * G ^ 2 - 928 * G * (2 : ℤ) ^ s -
      80 * ((2 : ℤ) ^ s) ^ 2 + 928 * G - 768 * (2 : ℤ) ^ s + 1121 : ℤ))
    (t0 := (262144 * ((2 : ℤ) ^ s) ^ 4 + 14848 * ((2 : ℤ) ^ s) ^ 2 - 108 * (2 : ℤ) ^ s + 28 : ℤ))
    (t1 := (768 * ((2 : ℤ) ^ s) ^ 2 - 4 * (2 : ℤ) ^ s + 1 : ℤ))
    (t2 := (0 : ℤ)) ?_ ?_ ?_).trans ?_
  · simp_t231
    linear_combination (16384 * ((2 : ℤ) ^ s) ^ 3 + 768 * G * (2 : ℤ) ^ s +
      2720 * (2 : ℤ) ^ s) * hG
  · simp_t231
    linear_combination (192 * (2 : ℤ) ^ s) * hG
  · simp_t231
    linear_combination (0) * hG
  · simp only [tor230]
    module

theorem phiU_t231_eq_t230 (h : Type230.Data s i F G) (h' : Type231.Data s i F G)
    (x : Torus (Type230.k s)) : (act231 h').φu x = (Type230.action h).φu x :=
  rfl

theorem phiR_t231_eq_t230 (h : Type230.Data s i F G) (h' : Type231.Data s i F G)
    (x : Torus (Type230.k s)) : (act231 h').φρ x = (Type230.action h).φρ x :=
  rfl

theorem phiU_gen1_exact_t230 (h : Type230.Data s i F G) :
    (Type230.action h).φu (gen (Type230.k s) 1) =
      (-2 * F + 2 * 2 ^ s : ℤ) • gen (Type230.k s) 0 + (0 : ℤ) • gen (Type230.k s) 1 +
        (1 : ℤ) • gen (Type230.k s) 2 := by
  conv_lhs => rw [gen_one_eq218]
  refine matAct_gens_eq _ _ 0 0 0 (t0 := 0) (t1 := 0) (t2 := 0) ?_ ?_ ?_ <;>
  · simp_t230
    ring

theorem phiR_gen0_t230 (h : Type230.Data s i F G) :
    (Type230.action h).φρ (gen (Type230.k s) 0) = gen (Type230.k s) 0 := by
  conv_lhs => rw [gen_zero_eq218]
  rw [phiR_apply_gens_t230 h]
  simp

end Ext220

end CFSG.CGT.Stroth77
