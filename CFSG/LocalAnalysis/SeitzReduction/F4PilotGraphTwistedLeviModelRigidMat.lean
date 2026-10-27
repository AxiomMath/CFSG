module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearPureGraph

public section

namespace CFSG.SeitzReduction.F4Pilot

open Matrix

variable {F : Type} [Field F]

@[expose] def rgU (c d : F) : Matrix (Fin 6) (Fin 6) F := 1 + single 1 2 c + single 5 4 d

@[expose] def rgUm (c d : F) : Matrix (Fin 6) (Fin 6) F := 1 + single 2 1 c + single 4 5 d

@[expose] def rgT (c : F) : Matrix (Fin 6) (Fin 6) F := 1 + single 2 5 c

@[expose] def rgTm (c : F) : Matrix (Fin 6) (Fin 6) F := 1 + single 5 2 c

@[expose] def rgX (c : F) : Matrix (Fin 6) (Fin 6) F := 1 + single 1 4 c

@[expose] def rgV (c d : F) : Matrix (Fin 6) (Fin 6) F := 1 + single 1 5 c + single 2 4 d

@[expose] def rgD (s : F) : Matrix (Fin 6) (Fin 6) F := diagonal ![1, s, s, 1, s⁻¹, s⁻¹]

@[expose] def rgPerm12 : Fin 6 → Fin 6 := ![0, 2, 1, 3, 5, 4]

@[expose] def rgPerm25 : Fin 6 → Fin 6 := ![0, 1, 5, 3, 4, 2]

@[expose] def rgP12 : Matrix (Fin 6) (Fin 6) F :=
  Matrix.of fun i j => if j = rgPerm12 i then 1 else 0

@[expose] def rgP25 : Matrix (Fin 6) (Fin 6) F :=
  Matrix.of fun i j => if j = rgPerm25 i then 1 else 0

theorem rg_blockSwapJ_apply (i j : Fin 6) :
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 :
      Matrix (Fin 6) (Fin 6) F) i j =
      if (j : ℕ) = i + 3 ∨ (i : ℕ) = j + 3 then 1 else 0 :=
  rfl

variable [CharP F 2]

omit [CharP F 2] in
theorem rgU_mul (c d c' d' : F) : rgU c d * rgU c' d' = rgU (c + c') (d + d') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rgU, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, Matrix.single_apply]
  all_goals ring

omit [CharP F 2] in
theorem rgU_zero : rgU (0 : F) 0 = 1 := by
  simp [rgU]

theorem rgU_mul_self (c d : F) : rgU c d * rgU c d = 1 := by
  rw [rgU_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, rgU_zero]

omit [CharP F 2] in
theorem rgP12_rgU_rgP12 (c d : F) : rgP12 * rgU c d * rgP12 = rgUm c d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rgP12, rgPerm12, rgU, rgUm, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply,
      Matrix.single_apply]

omit [CharP F 2] in
theorem rgP25_rgU_rgP25 (c d : F) : rgP25 * rgU c d * rgP25 = rgV c d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rgP25, rgPerm25, rgU, rgV, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply,
      Matrix.single_apply]

theorem rgT_rgU_rgT_rgU (c d : F) :
    rgT 1 * rgU c d * rgT 1 * rgU c d = rgV c d * rgX (c * d) := by
  have e1 : rgT 1 * rgU c d =
      1 + single 1 2 c + single 5 4 d + single 2 5 1 + single 2 4 d := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rgT, rgU, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, Matrix.single_apply]
  have e2 : (1 + single 1 2 c + single 5 4 d + single 2 5 1 + single 2 4 d) * rgT 1 =
      1 + single 1 2 c + single 5 4 d + single 2 4 d + single 1 5 c := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rgT, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, Matrix.single_apply,
        CharTwo.add_self_eq_zero]
  have e3 : (1 + single 1 2 c + single 5 4 d + single 2 4 d + single 1 5 c) * rgU c d =
      rgV c d * rgX (c * d) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rgU, rgV, rgX, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply,
        Matrix.single_apply, CharTwo.add_self_eq_zero]
  rw [e1, e2, e3]

omit [CharP F 2] in
theorem rgX_rgU_comm (t c d : F) : rgX t * rgU c d = rgU c d * rgX t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rgX, rgU, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, Matrix.single_apply]

omit [CharP F 2] in
theorem rgTm_rgU_comm (t c d : F) : rgTm t * rgU c d = rgU c d * rgTm t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rgTm, rgU, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, Matrix.single_apply]

omit [CharP F 2] in
theorem rgD_rgU_comm (s c d : F) : rgD s * rgU c d = rgU c d * rgD s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rgD, rgU, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, Matrix.single_apply,
      mul_comm]

omit [CharP F 2] in
theorem eq_of_rgV_mul_rgX_eq {c d a b : F} (h : rgV c d * rgX a = rgV c d * rgX b) : a = b := by
  have e := congrFun₂ h 1 4
  simpa [rgV, rgX, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, Matrix.single_apply]
    using e

omit [CharP F 2] in
theorem eq_of_rgU_eq {c d c' d' : F} (h : rgU c d = rgU c' d') : c = c' ∧ d = d' := by
  have e1 := congrFun₂ h 1 2
  have e2 := congrFun₂ h 5 4
  simp [rgU] at e1 e2
  exact ⟨e1, e2⟩

theorem rgU_rgUm_rgU_one : rgU (1 : F) 1 * rgUm 1 1 * rgU 1 1 = rgP12 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rgU, rgUm, rgP12, rgPerm12, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply,
      Matrix.single_apply, CharTwo.add_self_eq_zero]

theorem rgT_rgTm_rgT_one : rgT (1 : F) * rgTm 1 * rgT 1 = rgP25 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rgT, rgTm, rgP25, rgPerm25, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply,
      Matrix.single_apply, CharTwo.add_self_eq_zero]

omit [CharP F 2] in
theorem rgP12_rgT_rgP12 (t : F) : rgP12 * rgT t * rgP12 = rgX t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rgP12, rgPerm12, rgT, rgX, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply,
      Matrix.single_apply]

theorem rgU_rgUm_rgU {s : F} (hs : s ≠ 0) :
    rgU s s * rgUm s⁻¹ s⁻¹ * rgU s s =
      rgP12 * diagonal ![1, s⁻¹, s, 1, s, s⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rgU, rgUm, rgP12, rgPerm12, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply,
      Matrix.single_apply, hs, CharTwo.add_self_eq_zero]

theorem rgT_rgTm_rgT {r : F} (hr : r ≠ 0) :
    rgT r * rgTm r⁻¹ * rgT r = rgP25 * diagonal ![1, 1, r⁻¹, 1, 1, r] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rgT, rgTm, rgP25, rgPerm25, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply,
      Matrix.single_apply, hr, CharTwo.add_self_eq_zero]

theorem rgD_eq_prod {s : F} (hs : s ≠ 0) :
    rgU s s * rgUm s⁻¹ s⁻¹ * rgU s s * rgP12 *
        (rgT (s * s) * rgTm (s * s)⁻¹ * rgT (s * s) * rgP25) = rgD s := by
  have hss : s * s ≠ 0 := mul_ne_zero hs hs
  rw [rgU_rgUm_rgU hs, rgT_rgTm_rgT hss]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rgP12, rgPerm12, rgP25, rgPerm25, rgD, Matrix.mul_apply, Fin.sum_univ_six,
      Matrix.diagonal_apply, hs]

omit [CharP F 2] in
theorem rgU_map (φ : F →+* F) (c d : F) : (rgU c d).map φ = rgU (φ c) (φ d) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rgU]

theorem rg_eq_rgU_of_commute {s : F} (hs : s * s ≠ 1) (hs0 : s ≠ 0)
    {W : Matrix (Fin 6) (Fin 6) F}
    (hB : ∀ i j : Fin 6, (i = 0 ∨ i = 3 ∨ j = 0 ∨ j = 3) →
      W i j = (1 : Matrix (Fin 6) (Fin 6) F) i j)
    (hW : Wᵀ * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3 * W =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.blockSwapJ 6 3)
    (h1 : W * rgU 1 1 = rgU 1 1 * W) (hX : W * rgX 1 = rgX 1 * W)
    (hY : W * rgTm 1 = rgTm 1 * W) (hD : W * rgD s = rgD s * W) :
    W = rgU (W 1 2) (W 1 2) := by
  have b : ∀ i j : Fin 6, (i = 0 ∨ i = 3 ∨ j = 0 ∨ j = 3) → i ≠ j → W i j = 0 := by
    intro i j hij hne
    rw [hB i j hij, Matrix.one_apply_ne hne]
  have hsinv : s⁻¹ ≠ s := by
    intro h
    apply hs
    calc s * s = s * s⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel₀ hs0
  have x1 := congrFun₂ hX 1 4
  have x2 := congrFun₂ hX 2 4
  have x4 := congrFun₂ hX 4 4
  have x5 := congrFun₂ hX 5 4
  have x1' := congrFun₂ hX 1 1
  have x2' := congrFun₂ hX 1 2
  have x5' := congrFun₂ hX 1 5
  simp [rgX, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, Matrix.single_apply,
    b 0 4 (by decide) (by decide), b 3 4 (by decide) (by decide)] at x1 x2 x4 x5 x1' x2' x5'
  have y1 := congrFun₂ hY 1 2
  have y2 := congrFun₂ hY 2 2
  have y4 := congrFun₂ hY 4 2
  have y5 := congrFun₂ hY 5 2
  have y1' := congrFun₂ hY 5 1
  have y4' := congrFun₂ hY 5 4
  have y5' := congrFun₂ hY 5 5
  simp [rgTm, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, Matrix.single_apply,
    b 0 2 (by decide) (by decide), b 3 2 (by decide) (by decide)] at y1 y2 y4 y5 y1' y4' y5'
  have u12 := congrFun₂ h1 1 2
  simp [rgU, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply, Matrix.single_apply,
    b 0 2 (by decide) (by decide), b 3 2 (by decide) (by decide),
    b 1 0 (by decide) (by decide), b 1 3 (by decide) (by decide)] at u12
  have d14 := congrFun₂ hD 1 4
  have d52 := congrFun₂ hD 5 2
  simp only [rgD, Matrix.mul_diagonal, Matrix.diagonal_mul] at d14 d52
  have w14 : W 1 4 = 0 := by
    have e : W 1 4 * (s⁻¹ - s) = 0 := by
      have : W 1 4 * s⁻¹ = s * W 1 4 := d14
      linear_combination this
    rcases mul_eq_zero.1 e with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) hsinv
  have w52 : W 5 2 = 0 := by
    have e : W 5 2 * (s - s⁻¹) = 0 := by
      have : W 5 2 * s = s⁻¹ * W 5 2 := d52
      linear_combination this
    rcases mul_eq_zero.1 e with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h).symm hsinv
  have j14 := congrFun₂ hW 1 4
  have j24 := congrFun₂ hW 2 4
  simp [Matrix.mul_apply, Fin.sum_univ_six, rg_blockSwapJ_apply, Matrix.transpose_apply] at j14 j24
  have b31 := b 3 1 (by decide) (by decide)
  have b04 := b 0 4 (by decide) (by decide)
  have b01 := b 0 1 (by decide) (by decide)
  have b34 := b 3 4 (by decide) (by decide)
  have b32 := b 3 2 (by decide) (by decide)
  have b02 := b 0 2 (by decide) (by decide)
  rw [b31, b04, b01, b34, x4, x5, x2, w14] at j14
  rw [b32, b04, b02, b34, x2', w14, w52] at j24
  have h44 : W 4 4 = W 1 1 := by linear_combination -x1 + w14 - w14
  have h22 : W 2 2 = W 1 1 := by linear_combination -u12
  have h55 : W 5 5 = W 1 1 := by linear_combination y5 - w52 + w52 - u12
  have ha : W 1 1 = 1 := by
    have hsq : (W 1 1 + 1) * (W 1 1 + 1) = 0 := by
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      rw [h44] at j14
      linear_combination j14 + (W 1 1 + 1) * h2
    have := mul_self_eq_zero.1 hsq
    linear_combination this - CharTwo.two_eq_zero (R := F)
  have h54 : W 5 4 = W 1 2 := by
    rw [h44, h22, ha] at j24
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination j24 - W 1 2 * h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rgU, hB, ha, h22, h44, h55, h54, w14, w52, x2, x4, x5, x2', x5', y1, y2, y4']

end CFSG.SeitzReduction.F4Pilot
