module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Defs
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.RootWalk

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

private theorem d4Root_0 : d4Root 0 = (1 : ℤ) • (Pi.single (nd 0) 1 : Fin d4.rank → ℤ) := by
  decide +kernel

private theorem d4Root_1 : d4Root 1 = (1 : ℤ) • (Pi.single (nd 1) 1 : Fin d4.rank → ℤ) := by
  decide +kernel

private theorem d4Root_3 : d4Root 3 = (1 : ℤ) • (Pi.single (nd 3) 1 : Fin d4.rank → ℤ) := by
  decide +kernel

private theorem d4Root_4 : d4Root 4 = (-1 : ℤ) • (Pi.single (nd 0) 1 : Fin d4.rank → ℤ) := by
  decide +kernel

private theorem d4Root_6 : d4Root 6 = (-1 : ℤ) • (Pi.single (nd 1) 1 : Fin d4.rank → ℤ) := by
  decide +kernel

private theorem d4Root_10 : d4Root 10 = (-1 : ℤ) • (Pi.single (nd 3) 1 : Fin d4.rank → ℤ) := by
  decide +kernel

private theorem xOuter_one (c d e : K) : xOuter 1 c d e = xa 0 c * xa 1 d * xa 3 e := by
  simp only [xOuter, xa, d4Root_0, d4Root_1, d4Root_3]

private theorem xOuter_neg_one (c d e : K) : xOuter (-1) c d e = xa 4 c * xa 6 d * xa 10 e := by
  simp only [xOuter, xa, d4Root_4, d4Root_6, d4Root_10]

private theorem fP1_eq_xOuter (c : K) : fP1 σ hσ c = xOuter 1 c (σ c) (σ (σ c)) :=
  slShort_upper (σ := σ) hσ c

private theorem fM1_eq_xOuter (c : K) : fM1 σ hσ c = xOuter (-1) c (σ c) (σ (σ c)) :=
  slShort_lower (σ := σ) hσ c

theorem fP1_eq (c : K) : fP1 σ hσ c = xa 0 c * xa 1 (σ c) * xa 3 (σ (σ c)) := by
  rw [fP1_eq_xOuter, xOuter_one]

theorem fM1_eq (c : K) : fM1 σ hσ c = xa 4 c * xa 6 (σ c) * xa 10 (σ (σ c)) := by
  rw [fM1_eq_xOuter, xOuter_neg_one]

private theorem sl2Upper_add' {F : Type*} [Field F] (a b : F) :
    sl2Upper (a + b) = sl2Upper a * sl2Upper b := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Upper, coe_sl2Upper]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem sl2Lower_add' {F : Type*} [Field F] (a b : F) :
    sl2Lower (a + b) = sl2Lower a * sl2Lower b := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Lower, coe_sl2Lower, coe_sl2Lower]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem fP1_add (c c' : K) : fP1 σ hσ (c + c') = fP1 σ hσ c * fP1 σ hσ c' := by
  unfold fP1
  rw [sl2Upper_add', map_mul]

theorem fM1_add (c c' : K) : fM1 σ hσ (c + c') = fM1 σ hσ c * fM1 σ hσ c' := by
  unfold fM1
  rw [sl2Lower_add', map_mul]

variable (μ : Kˣ)

private theorem conj3 {G : Type*} [Group G] (A B C x : G) :
    A * B * C * x * (A * B * C)⁻¹ = A * (B * (C * x * C⁻¹) * B⁻¹) * A⁻¹ := by
  group

private theorem W1_conj_5 (u : K) : W1 K * xa 5 u * (W1 K)⁻¹ = xa 15 (-u) := by
  unfold W1
  rw [conj3, w4c_3_5, w4c_1_13, w4c_0_19]
  simp only [Units.val_one, inv_one, one_mul]

private theorem W1_conj_7 (u : K) : W1 K * xa 7 u * (W1 K)⁻¹ = xa 13 (-u) := by
  unfold W1
  rw [conj3, w4c_3_7, w4c_1_15, w4c_0_9]
  simp only [Units.val_one, inv_one, one_mul]

private theorem W1_conj_9 (u : K) : W1 K * xa 9 u * (W1 K)⁻¹ = xa 12 u := by
  unfold W1
  rw [conj3, w4c_3_9, w4c_1_2, w4c_0_7]
  simp only [Units.val_one, inv_one, one_mul, neg_neg]

private theorem W1_conj_11 (u : K) : W1 K * xa 11 u * (W1 K)⁻¹ = xa 20 (-u) := by
  unfold W1
  rw [conj3, w4c_3_11, w4c_1_18, w4c_0_21]
  simp only [Units.val_one, inv_one, one_mul]

private theorem W1_conj_14 (u : K) : W1 K * xa 14 u * (W1 K)⁻¹ = xa 18 (-u) := by
  unfold W1
  rw [conj3, w4c_3_14, w4c_1_20, w4c_0_16]
  simp only [Units.val_one, inv_one, one_mul]

private theorem W1_conj_16 (u : K) : W1 K * xa 16 u * (W1 K)⁻¹ = xa 17 u := by
  unfold W1
  rw [conj3, w4c_3_16, w4c_1_8, w4c_0_14]
  simp only [Units.val_one, inv_one, one_mul, neg_neg]

theorem fP2_eq (c : K) : fP2 σ hσ μ c =
    xa 5 ((μ : K) * c) * xa 7 (σ ((μ : K) * c)) * xa 9 (-σ (σ ((μ : K) * c))) := by
  unfold fP2 W0
  rw [fP1_eq, conj_triple, w4c_2_0, w4c_2_1, w4c_2_3]
  simp only [Units.val_one, inv_one, one_mul]

theorem fM2_eq (c : K) : fM2 σ hσ μ c =
    xa 11 (((μ⁻¹ : Kˣ) : K) * c) * xa 14 (σ (((μ⁻¹ : Kˣ) : K) * c)) *
      xa 16 (-σ (σ (((μ⁻¹ : Kˣ) : K) * c))) := by
  unfold fM2 W0
  rw [fM1_eq, conj_triple, w4c_2_4, w4c_2_6, w4c_2_10]
  simp only [Units.val_one, inv_one, one_mul]

theorem fP3_eq (c : K) : fP3 σ hσ μ c =
    xa 15 (-((μ : K) * c)) * xa 13 (-σ ((μ : K) * c)) * xa 12 (-σ (σ ((μ : K) * c))) := by
  unfold fP3
  rw [fP2_eq, conj_triple, W1_conj_5, W1_conj_7, W1_conj_9]

theorem fM3_eq (c : K) : fM3 σ hσ μ c =
    xa 20 (-(((μ⁻¹ : Kˣ) : K) * c)) * xa 18 (-σ (((μ⁻¹ : Kˣ) : K) * c)) *
      xa 17 (-σ (σ (((μ⁻¹ : Kˣ) : K) * c))) := by
  unfold fM3
  rw [fM2_eq, conj_triple, W1_conj_11, W1_conj_14, W1_conj_16]

theorem fP2_add (c c' : K) : fP2 σ hσ μ (c + c') = fP2 σ hσ μ c * fP2 σ hσ μ c' := by
  unfold fP2
  rw [mul_add, fP1_add]
  group

theorem fM2_add (c c' : K) : fM2 σ hσ μ (c + c') = fM2 σ hσ μ c * fM2 σ hσ μ c' := by
  unfold fM2
  rw [mul_add, fM1_add]
  group

theorem fP3_add (c c' : K) : fP3 σ hσ μ (c + c') = fP3 σ hσ μ c * fP3 σ hσ μ c' := by
  unfold fP3
  rw [fP2_add]
  group

theorem fM3_add (c c' : K) : fM3 σ hσ μ (c + c') = fM3 σ hσ μ c * fM3 σ hσ μ c' := by
  unfold fM3
  rw [fM2_add]
  group

private theorem map_upper' (F : Subfield K) (c : F) :
    Matrix.SpecialLinearGroup.map F.subtype (sl2Upper c) = sl2Upper (c : K) :=
  Subtype.ext (by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [coe_sl2Upper])

private theorem map_lower' (F : Subfield K) (c : F) :
    Matrix.SpecialLinearGroup.map F.subtype (sl2Lower c) = sl2Lower (c : K) :=
  Subtype.ext (by
    ext p q
    fin_cases p <;> fin_cases q <;> simp [coe_sl2Lower])

private theorem coe_psiMu (F : Subfield K) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((psiMu μ F g : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      psiMat μ F g := rfl

private theorem psiMu_upper (F : Subfield K) (c : F) :
    psiMu μ F (sl2Upper c) = sl2Upper ((μ : K) * (c : K)) := by
  apply Subtype.ext
  rw [coe_psiMu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [psiMat, coe_sl2Upper]

private theorem psiMu_lower (F : Subfield K) (c : F) :
    psiMu μ F (sl2Lower c) = sl2Lower (((μ⁻¹ : Kˣ) : K) * (c : K)) := by
  apply Subtype.ext
  rw [coe_psiMu]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [psiMat, coe_sl2Lower]

theorem theta1_upper (F : Subfield K) (c : F) :
    theta1 σ hσ F (sl2Upper c) = fP1 σ hσ (c : K) := by
  unfold theta1 fP1
  rw [MonoidHom.comp_apply, map_upper']

theorem theta1_lower (F : Subfield K) (c : F) :
    theta1 σ hσ F (sl2Lower c) = fM1 σ hσ (c : K) := by
  unfold theta1 fM1
  rw [MonoidHom.comp_apply, map_lower']

theorem theta2_upper (F : Subfield K) (c : F) :
    theta2 σ hσ μ F (sl2Upper c) = fP2 σ hσ μ (c : K) := by
  unfold theta2 fP2 fP1
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, psiMu_upper]

theorem theta2_lower (F : Subfield K) (c : F) :
    theta2 σ hσ μ F (sl2Lower c) = fM2 σ hσ μ (c : K) := by
  unfold theta2 fM2 fM1
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, psiMu_lower]

private theorem W1_eq_nHatE : W1 K = nHatE K (ng 1) := by
  unfold W1
  rw [w4_one, w4_one, w4_one]
  rfl

theorem theta1_w (F : Subfield K) : theta1 σ hσ F (wSL2 F) = W1 K := by
  rw [W1_eq_nHatE, nHatE_one_eq, wSL2, map_mul, map_mul, theta1_upper, theta1_lower,
    fP1_eq_xOuter, fM1_eq_xOuter]
  simp only [OneMemClass.coe_one, NegMemClass.coe_neg, map_one, map_neg]

private theorem w4_eq (j : Fin 4) (t : Kˣ) :
    w4 j t = xPar (rootOperatorFamily d4) ((1 : ℤ) • (Pi.single j 1 : Fin d4.rank → ℤ)) (t : K) *
      xPar (rootOperatorFamily d4) ((-1 : ℤ) • (Pi.single j 1 : Fin d4.rank → ℤ)) (-(t : K)⁻¹) *
        xPar (rootOperatorFamily d4) ((1 : ℤ) • (Pi.single j 1 : Fin d4.rank → ℤ)) (t : K) := by
  simp [w4, CFSG.LieType.Steinberg.weylElement]

private theorem mu1_coe : ((mu1 σ μ : Kˣ) : K) = σ (μ : K) := rfl

private theorem Nmu_eq : Nmu σ μ = xOuter 1 (μ : K) (σ μ) (σ (σ μ)) *
    xOuter (-1) (-(μ : K)⁻¹) (σ (-(μ : K)⁻¹)) (σ (σ (-(μ : K)⁻¹))) *
      xOuter 1 (μ : K) (σ μ) (σ (σ μ)) := by
  have p : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1 := Or.inl rfl
  have n : (-1 : ℤ) = 1 ∨ (-1 : ℤ) = -1 := Or.inr rfl
  have c01 := fun {s s' : ℤ} (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1) (c d : K) =>
    commute_xPar_outer (a := nd 0) (b := nd 1) (by decide) (by decide) (by decide) hs hs' c d
  have c03 := fun {s s' : ℤ} (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1) (c d : K) =>
    commute_xPar_outer (a := nd 0) (b := nd 3) (by decide) (by decide) (by decide) hs hs' c d
  have c13 := fun {s s' : ℤ} (hs : s = 1 ∨ s = -1) (hs' : s' = 1 ∨ s' = -1) (c d : K) =>
    commute_xPar_outer (a := nd 1) (b := nd 3) (by decide) (by decide) (by decide) hs hs' c d
  unfold Nmu
  rw [w4_eq, w4_eq, w4_eq]
  simp only [xOuter, mu1_coe, map_neg, map_inv₀]
  exact mul_rearrange_three (c01 n p _ _) (c01 p p _ _) (c01 p n _ _) (c03 n p _ _)
    (c13 n p _ _) (c03 p p _ _) (c13 p p _ _) (c03 p n _ _) (c13 p n _ _)

private theorem slSh_wMu : slSh σ hσ (sl2Upper (μ : K) * sl2Lower (-((μ⁻¹ : Kˣ) : K)) *
    sl2Upper (μ : K)) = Nmu σ μ := by
  rw [map_mul, map_mul]
  change fP1 σ hσ μ * fM1 σ hσ (-((μ⁻¹ : Kˣ) : K)) * fP1 σ hσ μ = _
  rw [fP1_eq_xOuter, fM1_eq_xOuter, Nmu_eq]
  simp only [Units.val_inv_eq_inv_val]

theorem theta2_w (F : Subfield K) : theta2 σ hσ μ F (wSL2 F) = Wtil2 σ μ := by
  have e : psiMu μ F (wSL2 F) =
      sl2Upper (μ : K) * sl2Lower (-((μ⁻¹ : Kˣ) : K)) * sl2Upper (μ : K) := by
    rw [wSL2, map_mul, map_mul, psiMu_upper, psiMu_lower]
    simp only [mul_one, mul_neg, OneMemClass.coe_one, NegMemClass.coe_neg]
  unfold theta2 Wtil2
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [e, slSh_wMu]

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
