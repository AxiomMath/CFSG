module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Forms
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityOpposition
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergRoot
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.RootWalk CFSG.RankThree.Chevalley

set_option linter.unusedSectionVars false


variable {K : Type} [Field K]

variable (K) in
@[expose] noncomputable def zA : adjointGroup d4 K :=
  W1 K * W0 K * W1 K * W0 K * (W1 K)⁻¹ * (W0 K)⁻¹

theorem zA_eq : zA K = W1 K * W0 K * W1 K * W0 K * (W1 K)⁻¹ * (W0 K)⁻¹ := rfl

private theorem coe_W0 :
    ((W0 K : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) = trialityMiddleRep K := by
  rw [trialityMiddleRep_eq]
  unfold W0
  rw [w4_one]
  rfl

private theorem coe_W1 :
    ((W1 K : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) = trialityOuterRep K := by
  rw [trialityOuterRep_eq]
  unfold W1
  rw [w4_one, w4_one, w4_one, Subgroup.coe_mul, Subgroup.coe_mul, mul_assoc]
  rfl

theorem coe_zA : ((zA K : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) = trialityOpposition K := by
  rw [zA_eq, trialityOpposition, trialityOppositionShift]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_W0, coe_W1]
  group

private theorem zA_conj_w4 (x : adjointGroup d4 K) :
    zA K * x * (zA K)⁻¹ =
      (MulAut.conj (w4 0 1) * MulAut.conj (w4 1 1) * MulAut.conj (w4 3 1) * MulAut.conj (w4 2 1) *
        MulAut.conj (w4 0 1) * MulAut.conj (w4 1 1) * MulAut.conj (w4 3 1) * MulAut.conj (w4 2 1) *
        MulAut.conj (w4 3 (-1)) * MulAut.conj (w4 1 (-1)) * MulAut.conj (w4 0 (-1)) *
        MulAut.conj (w4 2 (-1)) : MulAut (adjointGroup d4 K)) x := by
  have e0 : (w4 0 (1 : Kˣ))⁻¹ = w4 0 (-1) := w4_inv 0 1
  have e1 : (w4 1 (1 : Kˣ))⁻¹ = w4 1 (-1) := w4_inv 1 1
  have e2 : (w4 2 (1 : Kˣ))⁻¹ = w4 2 (-1) := w4_inv 2 1
  have e3 : (w4 3 (1 : Kˣ))⁻¹ = w4 3 (-1) := w4_inv 3 1
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [← e0, ← e1, ← e2, ← e3]
  unfold zA W1 W0
  group

theorem zc_0 (u : K) : zA K * xa 0 u * (zA K)⁻¹ = xa 4 (-u) := by
  rw [zA_conj_w4]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [w4c_2_0, w4c_0_5, w4c_1_2, w4c_3_7, w4c_2_15, w4c_3_15, w4c_1_7, w4c_0_2, w4c_2_5, w4c_3_0,
    w4c_1_0, w4c_0_0]
  refine congrArg (xa 4) ?_
  simp only [Units.val_neg, Units.val_one]
  ring

theorem zc_1 (u : K) : zA K * xa 1 u * (zA K)⁻¹ = xa 6 (-u) := by
  rw [zA_conj_w4]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [w4c_2_1, w4c_0_7, w4c_1_12, w4c_3_5, w4c_2_13, w4c_3_13, w4c_1_5, w4c_0_12, w4c_2_7, w4c_3_1,
    w4c_1_1, w4c_0_6]
  refine congrArg (xa 6) ?_
  simp only [Units.val_neg, Units.val_one]
  ring

theorem zc_3 (u : K) : zA K * xa 3 u * (zA K)⁻¹ = xa 10 (-u) := by
  rw [zA_conj_w4]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [w4c_2_3, w4c_0_9, w4c_1_13, w4c_3_19, w4c_2_12, w4c_3_12, w4c_1_19, w4c_0_13, w4c_2_9,
    w4c_3_3, w4c_1_10, w4c_0_10]
  refine congrArg (xa 10) ?_
  simp only [Units.val_neg, Units.val_one]
  ring

theorem zc_4 (u : K) : zA K * xa 4 u * (zA K)⁻¹ = xa 0 (-u) := by
  rw [zA_conj_w4]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [w4c_2_4, w4c_0_11, w4c_1_8, w4c_3_14, w4c_2_20, w4c_3_20, w4c_1_14, w4c_0_8, w4c_2_11,
    w4c_3_4, w4c_1_4, w4c_0_4]
  refine congrArg (xa 0) ?_
  simp only [Units.val_neg, Units.val_one]
  ring

theorem zc_6 (u : K) : zA K * xa 6 u * (zA K)⁻¹ = xa 1 (-u) := by
  rw [zA_conj_w4]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [w4c_2_6, w4c_0_14, w4c_1_17, w4c_3_11, w4c_2_18, w4c_3_18, w4c_1_11, w4c_0_17, w4c_2_14,
    w4c_3_6, w4c_1_6, w4c_0_1]
  refine congrArg (xa 1) ?_
  simp only [Units.val_neg, Units.val_one]
  ring

theorem zc_10 (u : K) : zA K * xa 10 u * (zA K)⁻¹ = xa 3 (-u) := by
  rw [zA_conj_w4]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [w4c_2_10, w4c_0_16, w4c_1_18, w4c_3_21, w4c_2_17, w4c_3_17, w4c_1_21, w4c_0_18, w4c_2_16,
    w4c_3_10, w4c_1_3, w4c_0_3]
  refine congrArg (xa 3) ?_
  simp only [Units.val_neg, Units.val_one]
  ring

theorem zc_5 (u : K) : zA K * xa 5 u * (zA K)⁻¹ = xa 11 u := by
  rw [zA_conj_w4]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [w4c_2_5, w4c_0_0, w4c_1_4, w4c_3_4, w4c_2_4, w4c_3_11, w4c_1_18, w4c_0_21, w4c_2_20, w4c_3_20,
    w4c_1_14, w4c_0_8]
  refine congrArg (xa 11) ?_
  simp only [Units.val_neg, Units.val_one]
  ring

theorem zc_7 (u : K) : zA K * xa 7 u * (zA K)⁻¹ = xa 14 u := by
  rw [zA_conj_w4]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [w4c_2_7, w4c_0_1, w4c_1_1, w4c_3_6, w4c_2_6, w4c_3_14, w4c_1_20, w4c_0_16, w4c_2_18, w4c_3_18,
    w4c_1_11, w4c_0_17]
  refine congrArg (xa 14) ?_
  simp only [Units.val_neg, Units.val_one]
  ring

theorem zc_9 (u : K) : zA K * xa 9 u * (zA K)⁻¹ = xa 16 u := by
  rw [zA_conj_w4]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [w4c_2_9, w4c_0_3, w4c_1_3, w4c_3_3, w4c_2_10, w4c_3_16, w4c_1_8, w4c_0_14, w4c_2_17, w4c_3_17,
    w4c_1_21, w4c_0_18]
  refine congrArg (xa 16) ?_
  simp only [Units.val_neg, Units.val_one]
  ring

theorem zc_11 (u : K) : zA K * xa 11 u * (zA K)⁻¹ = xa 5 u := by
  rw [zA_conj_w4]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [w4c_2_11, w4c_0_4, w4c_1_0, w4c_3_0, w4c_2_0, w4c_3_5, w4c_1_13, w4c_0_19, w4c_2_15, w4c_3_15,
    w4c_1_7, w4c_0_2]
  refine congrArg (xa 5) ?_
  simp only [Units.val_neg, Units.val_one]
  ring

theorem zc_14 (u : K) : zA K * xa 14 u * (zA K)⁻¹ = xa 7 u := by
  rw [zA_conj_w4]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [w4c_2_14, w4c_0_6, w4c_1_6, w4c_3_1, w4c_2_1, w4c_3_7, w4c_1_15, w4c_0_9, w4c_2_13, w4c_3_13,
    w4c_1_5, w4c_0_12]
  refine congrArg (xa 7) ?_
  simp only [Units.val_neg, Units.val_one]
  ring

theorem zc_16 (u : K) : zA K * xa 16 u * (zA K)⁻¹ = xa 9 u := by
  rw [zA_conj_w4]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [w4c_2_16, w4c_0_10, w4c_1_10, w4c_3_10, w4c_2_3, w4c_3_9, w4c_1_2, w4c_0_7, w4c_2_12,
    w4c_3_12, w4c_1_19, w4c_0_13]
  refine congrArg (xa 9) ?_
  simp only [Units.val_neg, Units.val_one]
  ring

theorem zc_15 (u : K) : zA K * xa 15 u * (zA K)⁻¹ = xa 20 u := by
  rw [zA_conj_w4]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [w4c_2_15, w4c_0_15, w4c_1_19, w4c_3_13, w4c_2_5, w4c_3_0, w4c_1_0, w4c_0_0, w4c_2_4, w4c_3_11,
    w4c_1_18, w4c_0_21]
  refine congrArg (xa 20) ?_
  simp only [Units.val_neg, Units.val_one]
  ring

theorem zc_13 (u : K) : zA K * xa 13 u * (zA K)⁻¹ = xa 18 u := by
  rw [zA_conj_w4]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [w4c_2_13, w4c_0_13, w4c_1_9, w4c_3_15, w4c_2_7, w4c_3_1, w4c_1_1, w4c_0_6, w4c_2_6, w4c_3_14,
    w4c_1_20, w4c_0_16]
  refine congrArg (xa 18) ?_
  simp only [Units.val_neg, Units.val_one]
  ring

theorem zc_12 (u : K) : zA K * xa 12 u * (zA K)⁻¹ = xa 17 u := by
  rw [zA_conj_w4]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [w4c_2_12, w4c_0_12, w4c_1_7, w4c_3_2, w4c_2_9, w4c_3_3, w4c_1_10, w4c_0_10, w4c_2_10,
    w4c_3_16, w4c_1_8, w4c_0_14]
  refine congrArg (xa 17) ?_
  simp only [Units.val_neg, Units.val_one]
  ring

theorem zc_20 (u : K) : zA K * xa 20 u * (zA K)⁻¹ = xa 15 u := by
  rw [zA_conj_w4]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [w4c_2_20, w4c_0_20, w4c_1_21, w4c_3_18, w4c_2_11, w4c_3_4, w4c_1_4, w4c_0_4, w4c_2_0, w4c_3_5,
    w4c_1_13, w4c_0_19]
  refine congrArg (xa 15) ?_
  simp only [Units.val_neg, Units.val_one]
  ring

theorem zc_18 (u : K) : zA K * xa 18 u * (zA K)⁻¹ = xa 13 u := by
  rw [zA_conj_w4]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [w4c_2_18, w4c_0_18, w4c_1_16, w4c_3_20, w4c_2_14, w4c_3_6, w4c_1_6, w4c_0_1, w4c_2_1, w4c_3_7,
    w4c_1_15, w4c_0_9]
  refine congrArg (xa 13) ?_
  simp only [Units.val_neg, Units.val_one]
  ring

theorem zc_17 (u : K) : zA K * xa 17 u * (zA K)⁻¹ = xa 12 u := by
  rw [zA_conj_w4]
  simp only [MulAut.mul_apply, MulAut.conj_apply]
  rw [w4c_2_17, w4c_0_17, w4c_1_14, w4c_3_8, w4c_2_16, w4c_3_10, w4c_1_3, w4c_0_3, w4c_2_3, w4c_3_9,
    w4c_1_2, w4c_0_7]
  refine congrArg (xa 12) ?_
  simp only [Units.val_neg, Units.val_one]
  ring


private theorem conj_three_xa {g : adjointGroup d4 K} {a b c a' b' c' : ℕ} {x y z x' y' z' : K}
    (ha : g * xa a x * g⁻¹ = xa a' x') (hb : g * xa b y * g⁻¹ = xa b' y')
    (hc : g * xa c z * g⁻¹ = xa c' z') :
    g * (xa a x * xa b y * xa c z) * g⁻¹ = xa a' x' * xa b' y' * xa c' z' := by
  rw [conj_triple, ha, hb, hc]

private theorem triple_xa_eq {i j k : ℕ} {a a' b b' c c' : K} (ha : a = a') (hb : b = b')
    (hc : c = c') : xa i a * xa j b * xa k c = xa i a' * xa j b' * xa k c' := by
  subst ha hb hc
  rfl

private theorem aut_xa (ε : K ≃+* K) (a : ℕ) (u : K) :
    entrywiseAdjointAut d4 ε (xa a u) = xa a (ε u) :=
  CFSG.StandardType.AutSt.entrywiseAdjointAut_xPar ε (d4Root a) u

private theorem tau_of_conj {ε : K ≃+* K} {g h : adjointGroup d4 K}
    (H : zA K * entrywiseAdjointAut d4 ε g * (zA K)⁻¹ = h) :
    trialityOpposition K * Units.map (entrywiseHom ε.toRingHom)
        (g : ModGL TwistTag.D4.tag K) * (trialityOpposition K)⁻¹ =
      (h : ModGL TwistTag.D4.tag K) := by
  subst H
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_zA]
  rfl

private theorem key_mu (ε : K ≃+* K) (μ : Kˣ) (c : K) :
    ((μ⁻¹ : Kˣ) : K) * (((μ : K) * ε (μ : K)) * ε c) = ε ((μ : K) * c) := by
  have h : ((μ⁻¹ : Kˣ) : K) * (μ : K) = 1 := Units.inv_mul μ
  rw [map_mul]
  linear_combination (ε (μ : K) * ε c) * h

private theorem key_muinv (ε : K ≃+* K) (μ : Kˣ) (c : K) :
    (μ : K) * ((((μ⁻¹ : Kˣ) : K) * ε ((μ⁻¹ : Kˣ) : K)) * ε c) = ε (((μ⁻¹ : Kˣ) : K) * c) := by
  have h : (μ : K) * ((μ⁻¹ : Kˣ) : K) = 1 := Units.mul_inv μ
  rw [map_mul]
  linear_combination (ε ((μ⁻¹ : Kˣ) : K) * ε c) * h

theorem tau_fP1 {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) (ε : K ≃+* K)
    (hε : ∀ c, σ (ε c) = ε (σ c)) (c : K) :
    trialityOpposition K * Units.map (entrywiseHom ε.toRingHom)
        ((fP1 σ hσ c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) * (trialityOpposition K)⁻¹ =
      ((fM1 σ hσ (-(ε c)) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  refine tau_of_conj ?_
  rw [fP1_eq, map_mul, map_mul, aut_xa, aut_xa, aut_xa,
    conj_three_xa (zc_0 _) (zc_1 _) (zc_3 _), fM1_eq]
  exact triple_xa_eq rfl (by simp only [map_neg, hε]) (by simp only [map_neg, hε])

theorem tau_fM1 {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) (ε : K ≃+* K)
    (hε : ∀ c, σ (ε c) = ε (σ c)) (c : K) :
    trialityOpposition K * Units.map (entrywiseHom ε.toRingHom)
        ((fM1 σ hσ c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) * (trialityOpposition K)⁻¹ =
      ((fP1 σ hσ (-(ε c)) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  refine tau_of_conj ?_
  rw [fM1_eq, map_mul, map_mul, aut_xa, aut_xa, aut_xa,
    conj_three_xa (zc_4 _) (zc_6 _) (zc_10 _), fP1_eq]
  exact triple_xa_eq rfl (by simp only [map_neg, hε]) (by simp only [map_neg, hε])

theorem tau_fP2 {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) (ε : K ≃+* K)
    (hε : ∀ c, σ (ε c) = ε (σ c)) (μ : Kˣ) (c : K) :
    trialityOpposition K * Units.map (entrywiseHom ε.toRingHom)
        ((fP2 σ hσ μ c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) * (trialityOpposition K)⁻¹ =
      ((fM2 σ hσ μ (((μ : K) * ε (μ : K)) * ε c) : adjointGroup d4 K) :
        ModGL TwistTag.D4.tag K) := by
  refine tau_of_conj ?_
  rw [fP2_eq, map_mul, map_mul, aut_xa, aut_xa, aut_xa,
    conj_three_xa (zc_5 _) (zc_7 _) (zc_9 _), fM2_eq, key_mu]
  exact triple_xa_eq rfl (by simp only [hε]) (by simp only [map_neg, hε])

theorem tau_fM2 {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) (ε : K ≃+* K)
    (hε : ∀ c, σ (ε c) = ε (σ c)) (μ : Kˣ) (c : K) :
    trialityOpposition K * Units.map (entrywiseHom ε.toRingHom)
        ((fM2 σ hσ μ c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) * (trialityOpposition K)⁻¹ =
      ((fP2 σ hσ μ ((((μ⁻¹ : Kˣ) : K) * ε ((μ⁻¹ : Kˣ) : K)) * ε c) : adjointGroup d4 K) :
        ModGL TwistTag.D4.tag K) := by
  refine tau_of_conj ?_
  rw [fM2_eq, map_mul, map_mul, aut_xa, aut_xa, aut_xa,
    conj_three_xa (zc_11 _) (zc_14 _) (zc_16 _), fP2_eq, key_muinv]
  exact triple_xa_eq rfl (by simp only [hε]) (by simp only [map_neg, hε])

theorem tau_fP3 {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) (ε : K ≃+* K)
    (hε : ∀ c, σ (ε c) = ε (σ c)) (μ : Kˣ) (c : K) :
    trialityOpposition K * Units.map (entrywiseHom ε.toRingHom)
        ((fP3 σ hσ μ c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) * (trialityOpposition K)⁻¹ =
      ((fM3 σ hσ μ (((μ : K) * ε (μ : K)) * ε c) : adjointGroup d4 K) :
        ModGL TwistTag.D4.tag K) := by
  refine tau_of_conj ?_
  rw [fP3_eq, map_mul, map_mul, aut_xa, aut_xa, aut_xa,
    conj_three_xa (zc_15 _) (zc_13 _) (zc_12 _), fM3_eq, key_mu]
  exact triple_xa_eq (by simp only [map_neg, hε]) (by simp only [map_neg, hε])
    (by simp only [map_neg, hε])

theorem tau_fM3 {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) (ε : K ≃+* K)
    (hε : ∀ c, σ (ε c) = ε (σ c)) (μ : Kˣ) (c : K) :
    trialityOpposition K * Units.map (entrywiseHom ε.toRingHom)
        ((fM3 σ hσ μ c : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) * (trialityOpposition K)⁻¹ =
      ((fP3 σ hσ μ ((((μ⁻¹ : Kˣ) : K) * ε ((μ⁻¹ : Kˣ) : K)) * ε c) : adjointGroup d4 K) :
        ModGL TwistTag.D4.tag K) := by
  refine tau_of_conj ?_
  rw [fM3_eq, map_mul, map_mul, aut_xa, aut_xa, aut_xa,
    conj_three_xa (zc_20 _) (zc_18 _) (zc_17 _), fP3_eq, key_muinv]
  exact triple_xa_eq (by simp only [map_neg, hε]) (by simp only [map_neg, hε])
    (by simp only [map_neg, hε])

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
