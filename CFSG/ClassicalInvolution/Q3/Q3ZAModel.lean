module

public import CFSG.ClassicalInvolution.Q3.Q3ZADefs
public import CFSG.ClassicalInvolution.Q3.Q3WADict
public import CFSG.ClassicalInvolution.Q3.Q3ZAGlue
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Q3.Q3ZFrbFrame

public section

namespace CFSG.ClassicalInvolution.Q3.Q3ZA

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups
open Matrix

@[expose] noncomputable def usl (t : F3) : SL(2, F3) :=
  mkSL !![1, t; 0, 1] (by simp [Matrix.det_fin_two])

@[expose] noncomputable def lsl (t : F3) : SL(2, F3) :=
  mkSL !![1, 0; t, 1] (by simp [Matrix.det_fin_two])

theorem usl_add (s t : F3) : usl (s + t) = usl s * usl t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [usl, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem lsl_add (s t : F3) : lsl (s + t) = lsl s * lsl t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lsl, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem usl_zero : usl 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [usl]

theorem lsl_zero : lsl 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lsl]

theorem usl_one : usl 1 = uSL := rfl

theorem lsl_one : lsl 1 = lSL := rfl

theorem usl_inv (t : F3) : (usl t)⁻¹ = usl (-t) := by
  rw [inv_eq_iff_mul_eq_one, ← usl_add, add_neg_cancel, usl_zero]

theorem lsl_inv (t : F3) : (lsl t)⁻¹ = lsl (-t) := by
  rw [inv_eq_iff_mul_eq_one, ← lsl_add, add_neg_cancel, lsl_zero]


noncomputable abbrev sb : SL(2, F3) →* StatedSp 2 F3 :=
  shortBlock F3 (zero_ne_one : (0 : Fin 2) ≠ 1)

noncomputable abbrev bE0 : V4 := Pi.single (Sum.inl 0) 1
noncomputable abbrev bE1 : V4 := Pi.single (Sum.inl 1) 1
noncomputable abbrev bF0 : V4 := Pi.single (Sum.inr 0) 1
noncomputable abbrev bF1 : V4 := Pi.single (Sum.inr 1) 1

theorem sb_usl_e0 (t : F3) : mat 2 F3 (sb (usl t)) *ᵥ bE0 = bE0 := by
  have h := shortBlock_mulVec_inl_left (n := 2) (K := F3) (zero_ne_one : (0 : Fin 2) ≠ 1) (usl t)
  simpa [usl] using h

theorem sb_usl_e1 (t : F3) : mat 2 F3 (sb (usl t)) *ᵥ bE1 = bE1 + t • bE0 := by
  have h := shortBlock_mulVec_inl_right (n := 2) (K := F3) (zero_ne_one : (0 : Fin 2) ≠ 1) (usl t)
  simpa [usl, add_comm] using h

theorem sb_usl_f0 (t : F3) : mat 2 F3 (sb (usl t)) *ᵥ bF0 = bF0 - t • bF1 := by
  have h := shortBlock_mulVec_inr_left (n := 2) (K := F3) (zero_ne_one : (0 : Fin 2) ≠ 1) (usl t)
  simpa [usl_inv, usl, sub_eq_add_neg] using h

theorem sb_usl_f1 (t : F3) : mat 2 F3 (sb (usl t)) *ᵥ bF1 = bF1 := by
  have h := shortBlock_mulVec_inr_right (n := 2) (K := F3) (zero_ne_one : (0 : Fin 2) ≠ 1) (usl t)
  simpa [usl_inv, usl] using h

theorem sb_lsl_e0 (t : F3) : mat 2 F3 (sb (lsl t)) *ᵥ bE0 = bE0 + t • bE1 := by
  have h := shortBlock_mulVec_inl_left (n := 2) (K := F3) (zero_ne_one : (0 : Fin 2) ≠ 1) (lsl t)
  simpa [lsl] using h

theorem sb_lsl_e1 (t : F3) : mat 2 F3 (sb (lsl t)) *ᵥ bE1 = bE1 := by
  have h := shortBlock_mulVec_inl_right (n := 2) (K := F3) (zero_ne_one : (0 : Fin 2) ≠ 1) (lsl t)
  simpa [lsl] using h

theorem sb_lsl_f0 (t : F3) : mat 2 F3 (sb (lsl t)) *ᵥ bF0 = bF0 := by
  have h := shortBlock_mulVec_inr_left (n := 2) (K := F3) (zero_ne_one : (0 : Fin 2) ≠ 1) (lsl t)
  simpa [lsl_inv, lsl] using h

theorem sb_lsl_f1 (t : F3) : mat 2 F3 (sb (lsl t)) *ᵥ bF1 = bF1 - t • bF0 := by
  have h := shortBlock_mulVec_inr_right (n := 2) (K := F3) (zero_ne_one : (0 : Fin 2) ≠ 1) (lsl t)
  simpa [lsl_inv, lsl, sub_eq_add_neg, add_comm] using h


theorem lb_mulVec_inl (k : Fin 2) (A : SL(2, F3)) :
    mat 2 F3 (longBlock F3 2 k A) *ᵥ Pi.single (Sum.inl k) 1 =
      (A : Matrix (Fin 2) (Fin 2) F3) 0 0 • (Pi.single (Sum.inl k) 1 : V4) +
        (A : Matrix (Fin 2) (Fin 2) F3) 1 0 • (Pi.single (Sum.inr k) 1 : V4) := by
  funext r
  rw [mulVec_single_one_apply, mat_longBlock]
  by_cases h1 : r = Sum.inl k
  · subst h1
    simp [CFSG.LieType.Steinberg.Sp.blockMat]
  · by_cases h2 : r = Sum.inr k
    · subst h2
      simp [CFSG.LieType.Steinberg.Sp.blockMat]
    · simp [CFSG.LieType.Steinberg.Sp.blockMat, h1, h2, Matrix.one_apply]

theorem lb_mulVec_inr (k : Fin 2) (A : SL(2, F3)) :
    mat 2 F3 (longBlock F3 2 k A) *ᵥ Pi.single (Sum.inr k) 1 =
      (A : Matrix (Fin 2) (Fin 2) F3) 0 1 • (Pi.single (Sum.inl k) 1 : V4) +
        (A : Matrix (Fin 2) (Fin 2) F3) 1 1 • (Pi.single (Sum.inr k) 1 : V4) := by
  funext r
  rw [mulVec_single_one_apply, mat_longBlock]
  by_cases h1 : r = Sum.inl k
  · subst h1
    simp [CFSG.LieType.Steinberg.Sp.blockMat]
  · by_cases h2 : r = Sum.inr k
    · subst h2
      simp [CFSG.LieType.Steinberg.Sp.blockMat]
    · simp [CFSG.LieType.Steinberg.Sp.blockMat, h1, h2, Matrix.one_apply]

theorem lb_mulVec_other (k : Fin 2) (A : SL(2, F3)) {j : Fin 2 ⊕ Fin 2} (hj : j ∉ coords k) :
    mat 2 F3 (longBlock F3 2 k A) *ᵥ Pi.single j 1 = Pi.single j 1 := by
  funext r
  rw [mulVec_single_one_apply, mat_longBlock,
    blockMat_apply_of_not_mem k _ (fun h => hj h.2), Matrix.one_apply, Pi.single_apply]


theorem eq_of_mulVec_basis {x y : StatedSp 2 F3}
    (h0 : mat 2 F3 x *ᵥ bE0 = mat 2 F3 y *ᵥ bE0) (h1 : mat 2 F3 x *ᵥ bE1 = mat 2 F3 y *ᵥ bE1)
    (h2 : mat 2 F3 x *ᵥ bF0 = mat 2 F3 y *ᵥ bF0) (h3 : mat 2 F3 x *ᵥ bF1 = mat 2 F3 y *ᵥ bF1) :
    x = y := by
  refine mat_injective (Matrix.ext fun r t => ?_)
  have key : ∀ j : Fin 2 ⊕ Fin 2, mat 2 F3 x *ᵥ Pi.single j 1 = mat 2 F3 y *ᵥ Pi.single j 1 → 
      mat 2 F3 x r j = mat 2 F3 y r j := fun j h => by
    have := congrFun h r
    rwa [mulVec_single_one_apply, mulVec_single_one_apply] at this
  rcases t with t | t <;> fin_cases t
  · exact key _ h0
  · exact key _ h1
  · exact key _ h2
  · exact key _ h3


@[expose] noncomputable def weyl₀ : StatedSp 2 F3 := longBlock F3 2 0 wSL

theorem wSL_inv_apply : ((wSL⁻¹ : SL(2, F3)) : Matrix (Fin 2) (Fin 2) F3) = !![0, 1; -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wSL, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem wSL_mul_self : wSL * wSL = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl₁_mul_self : weyl₁ * weyl₁ = longInv F3 2 1 := by
  rw [weyl₁, longInv, ← map_mul, wSL_mul_self]

theorem weyl₀_mul_self : weyl₀ * weyl₀ = longInv F3 2 0 := by
  rw [weyl₀, longInv, ← map_mul, wSL_mul_self]

theorem w1_e0 : mat 2 F3 weyl₁ *ᵥ bE0 = bE0 :=
  lb_mulVec_other 1 wSL (by simp [coords])

theorem w1_f0 : mat 2 F3 weyl₁ *ᵥ bF0 = bF0 :=
  lb_mulVec_other 1 wSL (by simp [coords])

theorem w1_e1 : mat 2 F3 weyl₁ *ᵥ bE1 = bF1 := by
  rw [weyl₁, lb_mulVec_inl 1 wSL]
  simp [wSL]

theorem w1_f1 : mat 2 F3 weyl₁ *ᵥ bF1 = -bE1 := by
  rw [weyl₁, lb_mulVec_inr 1 wSL]
  simp [wSL]

theorem w0_e1 : mat 2 F3 weyl₀ *ᵥ bE1 = bE1 :=
  lb_mulVec_other 0 wSL (by simp [coords])

theorem w0_f1 : mat 2 F3 weyl₀ *ᵥ bF1 = bF1 :=
  lb_mulVec_other 0 wSL (by simp [coords])

theorem w0_e0 : mat 2 F3 weyl₀ *ᵥ bE0 = bF0 := by
  rw [weyl₀, lb_mulVec_inl 0 wSL]
  simp [wSL]

theorem w0_f0 : mat 2 F3 weyl₀ *ᵥ bF0 = -bE0 := by
  rw [weyl₀, lb_mulVec_inr 0 wSL]
  simp [wSL]

theorem w1i_e0 : mat 2 F3 weyl₁⁻¹ *ᵥ bE0 = bE0 := by
  rw [weyl₁, ← map_inv]
  exact lb_mulVec_other 1 _ (by simp [coords])

theorem w1i_f0 : mat 2 F3 weyl₁⁻¹ *ᵥ bF0 = bF0 := by
  rw [weyl₁, ← map_inv]
  exact lb_mulVec_other 1 _ (by simp [coords])

theorem w1i_e1 : mat 2 F3 weyl₁⁻¹ *ᵥ bE1 = -bF1 := by
  rw [weyl₁, ← map_inv, lb_mulVec_inl 1 wSL⁻¹, wSL_inv_apply]
  simp

theorem w1i_f1 : mat 2 F3 weyl₁⁻¹ *ᵥ bF1 = bE1 := by
  rw [weyl₁, ← map_inv, lb_mulVec_inr 1 wSL⁻¹, wSL_inv_apply]
  simp

theorem w0i_e1 : mat 2 F3 weyl₀⁻¹ *ᵥ bE1 = bE1 := by
  rw [weyl₀, ← map_inv]
  exact lb_mulVec_other 0 _ (by simp [coords])

theorem w0i_f1 : mat 2 F3 weyl₀⁻¹ *ᵥ bF1 = bF1 := by
  rw [weyl₀, ← map_inv]
  exact lb_mulVec_other 0 _ (by simp [coords])

theorem w0i_e0 : mat 2 F3 weyl₀⁻¹ *ᵥ bE0 = -bF0 := by
  rw [weyl₀, ← map_inv, lb_mulVec_inl 0 wSL⁻¹, wSL_inv_apply]
  simp

theorem w0i_f0 : mat 2 F3 weyl₀⁻¹ *ᵥ bF0 = bE0 := by
  rw [weyl₀, ← map_inv, lb_mulVec_inr 0 wSL⁻¹, wSL_inv_apply]
  simp


theorem sbU_eq : sbU = sb (usl 1) := rfl

theorem sbL_eq : sbL = sb (lsl 1) := rfl

theorem sb_usl_inv (t : F3) : (sb (usl t))⁻¹ = sb (usl (-t)) := by
  rw [← map_inv, usl_inv]

theorem sb_lsl_inv (t : F3) : (sb (lsl t))⁻¹ = sb (lsl (-t)) := by
  rw [← map_inv, lsl_inv]

theorem li_inl (k : Fin 2) :
    mat 2 F3 (longInv F3 2 k) *ᵥ Pi.single (Sum.inl k) 1 = -(Pi.single (Sum.inl k) 1 : V4) := by
  have h := lb_mulVec_inl k (-1)
  simpa [longInv] using h

theorem li_inr (k : Fin 2) :
    mat 2 F3 (longInv F3 2 k) *ᵥ Pi.single (Sum.inr k) 1 = -(Pi.single (Sum.inr k) 1 : V4) := by
  have h := lb_mulVec_inr k (-1)
  simpa [longInv] using h

theorem li_other (k : Fin 2) {j : Fin 2 ⊕ Fin 2} (hj : j ∉ coords k) :
    mat 2 F3 (longInv F3 2 k) *ᵥ Pi.single j 1 = Pi.single j 1 :=
  lb_mulVec_other k (-1) hj

theorem li0_e0 : mat 2 F3 (longInv F3 2 0) *ᵥ bE0 = -bE0 := li_inl 0
theorem li0_f0 : mat 2 F3 (longInv F3 2 0) *ᵥ bF0 = -bF0 := li_inr 0
theorem li0_e1 : mat 2 F3 (longInv F3 2 0) *ᵥ bE1 = bE1 := li_other 0 (by simp [coords])
theorem li0_f1 : mat 2 F3 (longInv F3 2 0) *ᵥ bF1 = bF1 := li_other 0 (by simp [coords])
theorem li1_e1 : mat 2 F3 (longInv F3 2 1) *ᵥ bE1 = -bE1 := li_inl 1
theorem li1_f1 : mat 2 F3 (longInv F3 2 1) *ᵥ bF1 = -bF1 := li_inr 1
theorem li1_e0 : mat 2 F3 (longInv F3 2 1) *ᵥ bE0 = bE0 := li_other 1 (by simp [coords])
theorem li1_f0 : mat 2 F3 (longInv F3 2 1) *ᵥ bF0 = bF0 := li_other 1 (by simp [coords])

local macro "act_simp" : tactic =>
  `(tactic| simp only [map_mul, ← Matrix.mulVec_mulVec, sbU_eq, sbL_eq, sb_usl_inv, sb_lsl_inv,
    sb_usl_e0, sb_usl_e1, sb_usl_f0, sb_usl_f1, sb_lsl_e0, sb_lsl_e1, sb_lsl_f0, sb_lsl_f1,
    w1_e0, w1_e1, w1_f0, w1_f1, w0_e0, w0_e1, w0_f0, w0_f1, w1i_e0, w1i_e1, w1i_f0, w1i_f1,
    w0i_e0, w0i_e1, w0i_f0, w0i_f1, li0_e0, li0_e1, li0_f0, li0_f1, li1_e0, li1_e1, li1_f0,
    li1_f1, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul, Matrix.mulVec_sub])

theorem weyl₁_conj_conj : weyl₁ * (weyl₁ * sbU * weyl₁⁻¹) * weyl₁⁻¹ = sbU⁻¹ := by
  have h : weyl₁ * (weyl₁ * sbU * weyl₁⁻¹) * weyl₁⁻¹ =
      longInv F3 2 1 * sbU * (longInv F3 2 1)⁻¹ := by
    rw [← weyl₁_mul_self]
    group
  rw [h, mul_inv_eq_iff_eq_mul, sbU_eq, sb_usl_inv]
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (act_simp; try module)

theorem weyl₀_conj : weyl₀ * (weyl₁ * sbU * weyl₁⁻¹) * weyl₀⁻¹ = sbL⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul, sbL_eq, sb_lsl_inv]
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (act_simp; try module)

@[expose] noncomputable def swapElt : StatedSp 2 F3 := sb wSL * longInv F3 2 1

theorem sbw_e0 : mat 2 F3 (sb wSL) *ᵥ bE0 = bE1 := by
  rw [sb, shortBlock_mulVec_inl_left (n := 2) (K := F3) (zero_ne_one : (0 : Fin 2) ≠ 1) wSL]
  simp [wSL]

theorem sbw_e1 : mat 2 F3 (sb wSL) *ᵥ bE1 = -bE0 := by
  rw [sb, shortBlock_mulVec_inl_right (n := 2) (K := F3) (zero_ne_one : (0 : Fin 2) ≠ 1) wSL]
  simp [wSL]

theorem sbw_f0 : mat 2 F3 (sb wSL) *ᵥ bF0 = bF1 := by
  rw [sb, shortBlock_mulVec_inr_left (n := 2) (K := F3) (zero_ne_one : (0 : Fin 2) ≠ 1) wSL,
    wSL_inv_apply]
  simp

theorem sbw_f1 : mat 2 F3 (sb wSL) *ᵥ bF1 = -bF0 := by
  rw [sb, shortBlock_mulVec_inr_right (n := 2) (K := F3) (zero_ne_one : (0 : Fin 2) ≠ 1) wSL,
    wSL_inv_apply]
  simp

theorem swap_e0 : mat 2 F3 swapElt *ᵥ bE0 = bE1 := by
  simp only [swapElt, map_mul, ← Matrix.mulVec_mulVec, li1_e0, sbw_e0]

theorem swap_e1 : mat 2 F3 swapElt *ᵥ bE1 = bE0 := by
  simp only [swapElt, map_mul, ← Matrix.mulVec_mulVec, li1_e1, Matrix.mulVec_neg, sbw_e1, neg_neg]

theorem swap_f0 : mat 2 F3 swapElt *ᵥ bF0 = bF1 := by
  simp only [swapElt, map_mul, ← Matrix.mulVec_mulVec, li1_f0, sbw_f0]

theorem swap_f1 : mat 2 F3 swapElt *ᵥ bF1 = bF0 := by
  simp only [swapElt, map_mul, ← Matrix.mulVec_mulVec, li1_f1, Matrix.mulVec_neg, sbw_f1, neg_neg]

local macro "act_simp'" : tactic =>
  `(tactic| simp only [map_mul, ← Matrix.mulVec_mulVec, sb_usl_e0, sb_usl_e1, sb_usl_f0,
    sb_usl_f1, sb_lsl_e0, sb_lsl_e1, sb_lsl_f0, sb_lsl_f1, swap_e0, swap_e1, swap_f0, swap_f1,
    li0_e0, li0_e1, li0_f0, li0_f1, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul,
    Matrix.mulVec_sub, map_one, Matrix.one_mulVec])

theorem swapElt_mul_self : swapElt * swapElt = 1 := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> act_simp'

theorem swapElt_inv : swapElt⁻¹ = swapElt := inv_eq_of_mul_eq_one_right swapElt_mul_self

theorem swap_mul_lb (x : SL(2, F3)) :
    swapElt * longBlock F3 2 0 x = longBlock F3 2 1 x * swapElt := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_
  · simp only [map_mul, ← Matrix.mulVec_mulVec, swap_e0, lb_mulVec_inl 0 x, lb_mulVec_inl 1 x,
      Matrix.mulVec_add, Matrix.mulVec_smul, swap_f0]
  · simp only [map_mul, ← Matrix.mulVec_mulVec, swap_e1, lb_mulVec_other 0 x (j := Sum.inl 1)
      (by simp [coords]), lb_mulVec_other 1 x (j := Sum.inl 0) (by simp [coords])]
  · simp only [map_mul, ← Matrix.mulVec_mulVec, swap_f0, lb_mulVec_inr 0 x, lb_mulVec_inr 1 x,
      Matrix.mulVec_add, Matrix.mulVec_smul, swap_e0]
  · simp only [map_mul, ← Matrix.mulVec_mulVec, swap_f1, lb_mulVec_other 0 x (j := Sum.inr 1)
      (by simp [coords]), lb_mulVec_other 1 x (j := Sum.inr 0) (by simp [coords])]

theorem swap_mul_sbU (t : F3) : swapElt * sb (usl t) = sb (lsl t) * swapElt := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (act_simp'; try module)

theorem swap_mul_sbL (t : F3) : swapElt * sb (lsl t) = sb (usl t) * swapElt := by
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (act_simp'; try module)

theorem iota_apply (x : StatedSp 2 F3) : iotaHom x = longInv F3 2 0 * x * (longInv F3 2 0)⁻¹ := rfl

theorem iota_sb_usl (t : F3) : iotaHom (sb (usl t)) = sb (usl (-t)) := by
  rw [iota_apply, mul_inv_eq_iff_eq_mul]
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (act_simp'; try module)

theorem iota_sb_lsl (t : F3) : iotaHom (sb (lsl t)) = sb (lsl (-t)) := by
  rw [iota_apply, mul_inv_eq_iff_eq_mul]
  refine eq_of_mulVec_basis ?_ ?_ ?_ ?_ <;> (act_simp'; try module)

end CFSG.ClassicalInvolution.Q3.Q3ZA
