module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Forms
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.RootWalk

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] {σ : K →+* K} {F : Subfield K} {d μ : Kˣ} (H : FrameHyp σ F d μ)

private theorem conj3 {g : adjointGroup d4 K} {a b c a' b' c' : ℕ} {x y z x' y' z' : K}
    (ha : g * xa a x * g⁻¹ = xa a' x') (hb : g * xa b y * g⁻¹ = xa b' y')
    (hc : g * xa c z * g⁻¹ = xa c' z') :
    g * (xa a x * xa b y * xa c z) * g⁻¹ = xa a' x' * xa b' y' * xa c' z' := by
  rw [conj_triple, ha, hb, hc]

private theorem triple_eq {i j k : ℕ} {a a' b b' c c' : K} (ha : a = a') (hb : b = b')
    (hc : c = c') : xa i a * xa j b * xa k c = xa i a' * xa j b' * xa k c' := by
  subst ha hb hc
  rfl

private theorem W1_conj {G : Type*} [Group G] (g h k x : G) :
    (g * h * k) * x * (g * h * k)⁻¹ = g * (h * (k * x * k⁻¹) * h⁻¹) * g⁻¹ := by
  group

theorem e2_id (c : K) : W1 K * fP3 σ H.sigma3 μ c * (W1 K)⁻¹ = fP2 σ H.sigma3 μ (-c) := by
  rw [fP3_eq, fP2_eq]
  unfold W1
  rw [W1_conj]
  rw [conj3 (w4c_3_15 _ _) (w4c_3_13 _ _) (w4c_3_12 _ _)]
  rw [conj3 (w4c_1_7 _ _) (w4c_1_5 _ _) (w4c_1_19 _ _)]
  rw [conj3 (w4c_0_2 _ _) (w4c_0_12 _ _) (w4c_0_13 _ _)]
  apply triple_eq
  · simp only [Units.val_one, inv_one, one_mul, mul_neg, neg_neg]
  · simp only [Units.val_one, inv_one, one_mul, mul_neg, neg_neg, map_neg]
  · simp only [Units.val_one, inv_one, one_mul, mul_neg, neg_neg, map_neg]

theorem e4_id (c : K) : W1 K * fM3 σ H.sigma3 μ c * (W1 K)⁻¹ = fM2 σ H.sigma3 μ (-c) := by
  rw [fM3_eq, fM2_eq]
  unfold W1
  rw [W1_conj]
  rw [conj3 (w4c_3_20 _ _) (w4c_3_18 _ _) (w4c_3_17 _ _)]
  rw [conj3 (w4c_1_14 _ _) (w4c_1_11 _ _) (w4c_1_21 _ _)]
  rw [conj3 (w4c_0_8 _ _) (w4c_0_17 _ _) (w4c_0_18 _ _)]
  apply triple_eq
  · simp only [Units.val_one, inv_one, one_mul, mul_neg, neg_neg]
  · simp only [Units.val_one, inv_one, one_mul, mul_neg, neg_neg, map_neg]
  · simp only [Units.val_one, inv_one, one_mul, mul_neg, neg_neg, map_neg]

private theorem Wtil2_conj (x : adjointGroup d4 K) :
    Wtil2 σ μ * x * (Wtil2 σ μ)⁻¹ =
      w4 2 1 * (w4 0 μ * (w4 1 (mu1 σ μ) * (w4 3 (mu1 σ (mu1 σ μ)) *
        (w4 2 (-1) * x * (w4 2 (-1))⁻¹) * (w4 3 (mu1 σ (mu1 σ μ)))⁻¹) *
        (w4 1 (mu1 σ μ))⁻¹) * (w4 0 μ)⁻¹) * (w4 2 1)⁻¹ := by
  have e : w4 2 (-1 : Kˣ) = (w4 2 1)⁻¹ := (w4_inv 2 1).symm
  rw [e]
  unfold Wtil2 W0 Nmu
  group

private theorem frame_d3 (H : FrameHyp σ F d μ) : (d : K) ^ 3 = 1 := by
  have h := congrArg Units.val H.d3
  simpa using h

private theorem frame_sm1 (H : FrameHyp σ F d μ) : σ (μ : K) = (d : K) ^ 2 * μ := by
  have h3 := frame_d3 H
  calc σ (μ : K) = (d : K) ^ 3 * σ (μ : K) := by rw [h3, one_mul]
    _ = (d : K) ^ 2 * ((d : K) * σ (μ : K)) := by ring
    _ = (d : K) ^ 2 * μ := by rw [H.sm]

private theorem frame_sm2 (H : FrameHyp σ F d μ) : σ (σ (μ : K)) = (d : K) * μ := by
  have h3 := frame_d3 H
  rw [frame_sm1 H, map_mul, map_pow, H.sd, frame_sm1 H]
  linear_combination ((d : K) * μ) * h3

private theorem frame_mu1 (H : FrameHyp σ F d μ) : ((mu1 σ μ : Kˣ) : K) = (d : K) ^ 2 * μ :=
  frame_sm1 H

private theorem frame_mu2 (H : FrameHyp σ F d μ) :
    ((mu1 σ (mu1 σ μ) : Kˣ) : K) = (d : K) * μ := by
  have h : ((mu1 σ (mu1 σ μ) : Kˣ) : K) = σ (σ (μ : K)) := rfl
  rw [h]
  exact frame_sm2 H

theorem f1_id (c : K) :
    Wtil2 σ μ * fP1 σ H.sigma3 c * (Wtil2 σ μ)⁻¹ = fP3 σ H.sigma3 μ (-c) := by
  rw [Wtil2_conj, fP1_eq, fP3_eq]
  rw [conj3 (w4c_2_0 _ _) (w4c_2_1 _ _) (w4c_2_3 _ _)]
  rw [conj3 (w4c_3_5 _ _) (w4c_3_7 _ _) (w4c_3_9 _ _)]
  rw [conj3 (w4c_1_13 _ _) (w4c_1_15 _ _) (w4c_1_2 _ _)]
  rw [conj3 (w4c_0_19 _ _) (w4c_0_9 _ _) (w4c_0_7 _ _)]
  rw [conj3 (w4c_2_15 _ _) (w4c_2_13 _ _) (w4c_2_12 _ _)]
  have h3 := frame_d3 H
  apply triple_eq
  · rw [frame_mu2 H, frame_mu1 H]
    simp only [Units.val_neg, Units.val_one]
    field_simp
    linear_combination c * h3
  · rw [frame_mu2 H, frame_mu1 H]
    simp only [Units.val_neg, Units.val_one, map_neg, map_mul]
    rw [frame_sm1 H]
    field_simp
    linear_combination (-σ c) * h3
  · rw [frame_mu2 H, frame_mu1 H]
    simp only [Units.val_neg, Units.val_one, map_neg, map_mul]
    rw [frame_sm2 H]
    field_simp

theorem f2_id (c : K) :
    Wtil2 σ μ * fP3 σ H.sigma3 μ c * (Wtil2 σ μ)⁻¹ = fP1 σ H.sigma3 c := by
  rw [Wtil2_conj, fP3_eq, fP1_eq]
  rw [conj3 (w4c_2_15 _ _) (w4c_2_13 _ _) (w4c_2_12 _ _)]
  rw [conj3 (w4c_3_15 _ _) (w4c_3_13 _ _) (w4c_3_12 _ _)]
  rw [conj3 (w4c_1_7 _ _) (w4c_1_5 _ _) (w4c_1_19 _ _)]
  rw [conj3 (w4c_0_2 _ _) (w4c_0_12 _ _) (w4c_0_13 _ _)]
  rw [conj3 (w4c_2_5 _ _) (w4c_2_7 _ _) (w4c_2_9 _ _)]
  have h3 := frame_d3 H
  apply triple_eq
  · rw [frame_mu2 H, frame_mu1 H]
    simp only [Units.val_neg, Units.val_one, map_neg, map_mul]
    field_simp
    linear_combination (-c) * h3
  · rw [frame_mu2 H, frame_mu1 H]
    simp only [Units.val_neg, Units.val_one, map_neg, map_mul]
    rw [frame_sm1 H]
    field_simp
    linear_combination σ c * h3
  · rw [frame_mu2 H, frame_mu1 H]
    simp only [Units.val_neg, Units.val_one, map_neg, map_mul]
    rw [frame_sm2 H]
    field_simp

theorem f3_id (c : K) :
    Wtil2 σ μ * fM1 σ H.sigma3 c * (Wtil2 σ μ)⁻¹ = fM3 σ H.sigma3 μ (-c) := by
  rw [Wtil2_conj, fM1_eq, fM3_eq]
  rw [conj3 (w4c_2_4 _ _) (w4c_2_6 _ _) (w4c_2_10 _ _)]
  rw [conj3 (w4c_3_11 _ _) (w4c_3_14 _ _) (w4c_3_16 _ _)]
  rw [conj3 (w4c_1_18 _ _) (w4c_1_20 _ _) (w4c_1_8 _ _)]
  rw [conj3 (w4c_0_21 _ _) (w4c_0_16 _ _) (w4c_0_14 _ _)]
  rw [conj3 (w4c_2_20 _ _) (w4c_2_18 _ _) (w4c_2_17 _ _)]
  have h3 := frame_d3 H
  apply triple_eq
  · rw [frame_mu2 H, frame_mu1 H]
    simp only [Units.val_neg, Units.val_one, map_neg, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    field_simp
    linear_combination (-c) * h3
  · rw [frame_mu2 H, frame_mu1 H]
    simp only [Units.val_neg, Units.val_one, map_neg, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    rw [frame_sm1 H]
    field_simp
    linear_combination σ c * h3
  · rw [frame_mu2 H, frame_mu1 H]
    simp only [Units.val_neg, Units.val_one, map_neg, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    rw [frame_sm2 H]
    field_simp

theorem f4_id (c : K) :
    Wtil2 σ μ * fM3 σ H.sigma3 μ c * (Wtil2 σ μ)⁻¹ = fM1 σ H.sigma3 c := by
  rw [Wtil2_conj, fM3_eq, fM1_eq]
  rw [conj3 (w4c_2_20 _ _) (w4c_2_18 _ _) (w4c_2_17 _ _)]
  rw [conj3 (w4c_3_20 _ _) (w4c_3_18 _ _) (w4c_3_17 _ _)]
  rw [conj3 (w4c_1_14 _ _) (w4c_1_11 _ _) (w4c_1_21 _ _)]
  rw [conj3 (w4c_0_8 _ _) (w4c_0_17 _ _) (w4c_0_18 _ _)]
  rw [conj3 (w4c_2_11 _ _) (w4c_2_14 _ _) (w4c_2_16 _ _)]
  have h3 := frame_d3 H
  apply triple_eq
  · rw [frame_mu2 H, frame_mu1 H]
    simp only [Units.val_neg, Units.val_one, map_neg, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    field_simp
    linear_combination c * h3
  · rw [frame_mu2 H, frame_mu1 H]
    simp only [Units.val_neg, Units.val_one, map_neg, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    rw [frame_sm1 H]
    field_simp
    linear_combination (-σ c) * h3
  · rw [frame_mu2 H, frame_mu1 H]
    simp only [Units.val_neg, Units.val_one, map_neg, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    rw [frame_sm2 H]
    field_simp

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
