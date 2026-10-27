module

public import CFSG.CGT.Stroth77.Extension24Torus
public import CFSG.CGT.Stroth77.TypesMore

local notation "𝔤" s:max j:max => CFSG.CGT.Stroth77.gen (CFSG.CGT.Stroth77.Type100.k (s + 1)) j

public section

namespace CFSG.CGT.Stroth77

theorem pow_zsmul_tor310 {t : ℕ} (m x y z : ℤ) :
    (m * 2 ^ (t + 1)) • tor300 (t + 1) x y z = 0 := by
  rw [show m * 2 ^ (t + 1) = (m * 2 ^ t) * 2 by ring, mul_smul, two_zsmul_tor300, smul_zero]

theorem neg_two_zsmul_tor310 {s : ℕ} (x y z : ℤ) : (-2 : ℤ) • tor300 s x y z = 0 := by
  rw [show (-2 : ℤ) = -1 * 2 by norm_num, mul_smul, two_zsmul_tor300, smul_zero]

theorem lifts310 {t : ℕ}
    (V W U R : Torus (Type100.k (t + 1 + 1)) →+ Torus (Type100.k (t + 1 + 1)))
    (hrels : SigmaFourRels V W U R)
    (hR0 : R (𝔤 (t + 1) 0) = (𝔤 (t + 1) 0)) (hR1 : R (𝔤 (t + 1) 1) = (𝔤 (t + 1) 2))
    (hR2 : R (𝔤 (t + 1) 2) =
      (-2 : ℤ) • (𝔤 (t + 1) 0) + (-1 : ℤ) • (𝔤 (t + 1) 1) + (-1 : ℤ) • (𝔤 (t + 1) 2))
    (hU0 : U (𝔤 (t + 1) 0) = (𝔤 (t + 1) 0) + tor300 (t + 1) 1 0 0)
    (hU1 : (2 : ℤ) • U (𝔤 (t + 1) 1) = (2 : ℤ) • (𝔤 (t + 1) 2))
    (hV0 : V (𝔤 (t + 1) 0) = (-3 : ℤ) • (𝔤 (t + 1) 0) + (-2 : ℤ) • (𝔤 (t + 1) 1) +
      (-2 : ℤ) • (𝔤 (t + 1) 2) + tor300 (t + 1) 0 1 0)
    (hV1 : (2 : ℤ) • V (𝔤 (t + 1) 1) =
      (4 : ℤ) • (𝔤 (t + 1) 0) + (2 : ℤ) • (𝔤 (t + 1) 1) + (4 : ℤ) • (𝔤 (t + 1) 2))
    (hV2 : (2 : ℤ) • V (𝔤 (t + 1) 2) =
      (4 : ℤ) • (𝔤 (t + 1) 0) + (4 : ℤ) • (𝔤 (t + 1) 1) + (2 : ℤ) • (𝔤 (t + 1) 2)) :
    ∃ x q : ℤ, U (𝔤 (t + 1) 1) = (𝔤 (t + 1) 2) + tor300 (t + 1) 0 0 x ∧
      V (𝔤 (t + 1) 1) = (2 : ℤ) • (𝔤 (t + 1) 0) + (𝔤 (t + 1) 1) + (2 : ℤ) • (𝔤 (t + 1) 2) +
        tor300 (t + 1) 0 0 q ∧
      V (𝔤 (t + 1) 2) = (2 : ℤ) • (𝔤 (t + 1) 0) + (2 : ℤ) • (𝔤 (t + 1) 1) + (𝔤 (t + 1) 2) +
        tor300 (t + 1) 0 q 0 := by
  have hRRR : ∀ w, R (R (R w)) = w := fun w => DFunLike.congr_fun hrels.rho_cube w
  have hUU : ∀ w, U (U w) = w := fun w => DFunLike.congr_fun hrels.u_sq w
  have hRURU : ∀ w, R (U (R (U w))) = w := fun w => DFunLike.congr_fun hrels.u_rho w
  have hVV : ∀ w, V (V w) = w := fun w => DFunLike.congr_fun hrels.uv_sq w
  have hUV : ∀ w, U (V w) = V (U w) := fun w => DFunLike.congr_fun hrels.uv_comm_u w
  have hRV : ∀ w, R (V w) = W (R w) := fun w => DFunLike.congr_fun hrels.uv_rho w
  have hUW : ∀ w, U (W w) = W (V (U w)) := fun w => DFunLike.congr_fun hrels.t_u w
  have hUR : ∀ w, U (R w) = R (R (U w)) := by
    intro w
    have h := hRURU (U w)
    rw [hUU] at h
    have h2 : R (R (R (U (R w)))) = R (R (U w)) := congrArg (fun v => R (R v)) h
    rw [hRRR] at h2
    exact h2
  obtain ⟨x0, x1, x2, hν⟩ := exists_tor300 (s := t + 1) (w := U (𝔤 (t + 1) 1) - (𝔤 (t + 1) 2))
    (by rw [smul_sub, hU1, sub_self])
  obtain ⟨p0, p1, p2, hω1⟩ := exists_tor300 (s := t + 1)
    (w := V (𝔤 (t + 1) 1) - ((2 : ℤ) • (𝔤 (t + 1) 0) + (𝔤 (t + 1) 1) + (2 : ℤ) • (𝔤 (t + 1) 2)))
        (by rw [smul_sub, hV1]; module)
  obtain ⟨r0, r1, r2, hω2⟩ := exists_tor300 (s := t + 1)
    (w := V (𝔤 (t + 1) 2) - ((2 : ℤ) • (𝔤 (t + 1) 0) + (2 : ℤ) • (𝔤 (t + 1) 1) + (𝔤 (t + 1) 2)))
        (by rw [smul_sub, hV2]; module)
  have hU1' : U (𝔤 (t + 1) 1) = (𝔤 (t + 1) 2) + tor300 (t + 1) x0 x1 x2 := by rw [← hν]; abel
  have hV1' : V (𝔤 (t + 1) 1) = (2 : ℤ) • (𝔤 (t + 1) 0) + (𝔤 (t + 1) 1) + (2 : ℤ) • (𝔤 (t + 1) 2) + tor300 (t + 1) p0 p1 p2 := by
    rw [← hω1]; abel
  have hV2' : V (𝔤 (t + 1) 2) = (2 : ℤ) • (𝔤 (t + 1) 0) + (2 : ℤ) • (𝔤 (t + 1) 1) + (𝔤 (t + 1) 2) + tor300 (t + 1) r0 r1 r2 := by
    rw [← hω2]; abel
  have hU0c : (2 : ℤ) • U (𝔤 (t + 1) 0) = (2 : ℤ) • (𝔤 (t + 1) 0) := by
    rw [hU0, smul_add _ _ (tor300 (t + 1) 1 0 0), two_zsmul_tor300, add_zero]
  have hV0c : (2 : ℤ) • V (𝔤 (t + 1) 0) = (2 : ℤ) • ((-3 : ℤ) • (𝔤 (t + 1) 0) +
      (-2 : ℤ) • (𝔤 (t + 1) 1) + (-2 : ℤ) • (𝔤 (t + 1) 2)) := by
    rw [hV0, smul_add _ _ (tor300 (t + 1) 0 1 0), two_zsmul_tor300, add_zero]
  have hV0c' : (-2 : ℤ) • V (𝔤 (t + 1) 0) = (-2 : ℤ) • ((-3 : ℤ) • (𝔤 (t + 1) 0) +
      (-2 : ℤ) • (𝔤 (t + 1) 1) + (-2 : ℤ) • (𝔤 (t + 1) 2)) := by
    rw [hV0, smul_add _ _ (tor300 (t + 1) 0 1 0), neg_two_zsmul_tor310, add_zero]
  have hRt : ∀ x y z : ℤ, R (tor300 (t + 1) x y z) = tor300 (t + 1) (x - 4 * z) (-z) (y - z) := by
    intro x y z
    simp only [tor300, map_add, map_zsmul, hR0, hR1, hR2]
    module
  have hRRf : R (R (𝔤 (t + 1) 2)) = (𝔤 (t + 1) 1) := by
    rw [hR2]
    simp only [map_add, map_zsmul, hR0, hR1, hR2]
    module
  have hU2' : U (𝔤 (t + 1) 2) = (𝔤 (t + 1) 1) + tor300 (t + 1) (x0 - 4 * x2 - 4 * (x1 - x2)) (-(x1 - x2))
      (-x2 - (x1 - x2)) := by
    rw [← hR1, hUR, hU1', map_add, map_add, hRRf, hRt, hRt]
  have hUt : ∀ x y z : ℤ, U (tor300 (t + 1) x y z) = tor300 (t + 1) x z y := by
    intro x y z
    have e : tor300 (t + 1) x y z =
        (x * 2 ^ (t + 1)) • (𝔤 (t + 1) 0) + (y * 2 ^ (t + 1 + 1)) • (𝔤 (t + 1) 1) + (z * 2 ^ (t + 1 + 1)) • (𝔤 (t + 1) 2) := rfl
    rw [e, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hU0, hU1', hU2']
    simp only [smul_add, pow_succ_zsmul_tor300, pow_zsmul_tor310, add_zero]
    simp only [tor300]
    module
  have hx1 : 2 ∣ x1 := by
    have h := hUU (𝔤 (t + 1) 1)
    rw [hU1', map_add, hU2', hUt] at h
    have key : tor300 (t + 1) ((x0 - 4 * x2 - 4 * (x1 - x2)) + x0) ((-(x1 - x2)) + x2)
        ((-x2 - (x1 - x2)) + x1) = tor300 (t + 1) 0 0 0 := by
      simp only [tor300] at h ⊢
      linear_combination (norm := module) h
    rw [tor300_eq_iff] at key
    omega
  have hVt : ∀ x y z : ℤ, V (tor300 (t + 1) x y z) =
      tor300 (t + 1) (-3 * x + 4 * y + 4 * z) (-x + y + 2 * z) (-x + 2 * y + z) := by
    intro x y z
    have e : tor300 (t + 1) x y z =
        (x * 2 ^ (t + 1)) • (𝔤 (t + 1) 0) + (y * 2 ^ (t + 1 + 1)) • (𝔤 (t + 1) 1) + (z * 2 ^ (t + 1 + 1)) • (𝔤 (t + 1) 2) := rfl
    rw [e, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hV0, hV1', hV2']
    simp only [smul_add, pow_succ_zsmul_tor300, pow_zsmul_tor310, add_zero]
    simp only [tor300]
    module
  have hp0 : 2 ∣ p0 := by
    have h := hVV (𝔤 (t + 1) 1)
    rw [hV1'] at h
    simp only [map_add, map_zsmul] at h
    rw [hV0c, hV1', hV2', hVt] at h
    have key : tor300 (t + 1) (p0 + 2 * r0 + (-3 * p0 + 4 * p1 + 4 * p2))
        (p1 + 2 * r1 + (-p0 + p1 + 2 * p2)) (p2 + 2 * r2 + (-p0 + 2 * p1 + p2)) =
        tor300 (t + 1) 0 0 0 := by
      simp only [tor300] at h ⊢
      linear_combination (norm := module) h
    rw [tor300_eq_iff] at key
    omega
  have hr : 2 ∣ p0 - r0 ∧ 2 ∣ x0 + p2 - r1 ∧ 2 ∣ x0 + p1 - r2 := by
    have h := hUV (𝔤 (t + 1) 1)
    rw [hV1', hU1'] at h
    simp only [map_add, map_zsmul] at h
    rw [hU0c, hU1', hU2', hUt, hV2', hVt] at h
    have key : tor300 (t + 1) (x0 + 2 * (x0 - 4 * x2 - 4 * (x1 - x2)) + p0 - r0 -
          (-3 * x0 + 4 * x1 + 4 * x2))
        (x1 + 2 * (-(x1 - x2)) + p2 - r1 - (-x0 + x1 + 2 * x2))
        (x2 + 2 * (-x2 - (x1 - x2)) + p1 - r2 - (-x0 + 2 * x1 + x2)) = tor300 (t + 1) 0 0 0 := by
      simp only [tor300] at h ⊢
      linear_combination (norm := module) h
    rw [tor300_eq_iff] at key
    omega
  have hW0 : W (𝔤 (t + 1) 0) = (𝔤 (t + 1) 0) + (2 : ℤ) • (𝔤 (t + 1) 1) +
      tor300 (t + 1) 0 0 1 := by
    have h := hRV (𝔤 (t + 1) 0)
    rw [hR0, hV0] at h
    rw [← h]
    simp only [map_add, map_zsmul, hR0, hR1, hR2, hRt]
    simp only [tor300]
    module
  have hW0c : (2 : ℤ) • W (𝔤 (t + 1) 0) = (2 : ℤ) • ((𝔤 (t + 1) 0) + (2 : ℤ) • (𝔤 (t + 1) 1)) := by
    rw [hW0, smul_add _ _ (tor300 (t + 1) 0 0 1), two_zsmul_tor300, add_zero]
  have hW2 : W (𝔤 (t + 1) 2) = (-2 : ℤ) • (𝔤 (t + 1) 0) + (-2 : ℤ) • (𝔤 (t + 1) 1) + (-1 : ℤ) • (𝔤 (t + 1) 2) +
      tor300 (t + 1) (p0 - 4 * p2) (-p2) (p1 - p2) := by
    have h := hRV (𝔤 (t + 1) 1)
    rw [hR1, hV1'] at h
    rw [← h]
    simp only [map_add, map_zsmul, hR0, hR1, hR2, hRt]
    module
  have hW1 : W (𝔤 (t + 1) 1) = -(𝔤 (t + 1) 1) - tor300 (t + 1) (p0 - 4 * p2) (-p2) (p1 - p2) -
      tor300 (t + 1) (r0 - 4 * r2) (-r2) (r1 - r2) := by
    have h := hRV (R (𝔤 (t + 1) 2))
    rw [hRRf] at h
    rw [← h, hR2]
    simp only [map_add, map_zsmul, hV0c', hV1', hV2']
    simp only [map_add, map_zsmul, hR0, hR1, hR2, hRt]
    module
  have hWt : ∀ x y z : ℤ, W (tor300 (t + 1) x y z) = tor300 (t + 1) (x - 4 * z) (x - y - 2 * z) (-z) := by
    intro x y z
    have e : tor300 (t + 1) x y z =
        (x * 2 ^ (t + 1)) • (𝔤 (t + 1) 0) + (y * 2 ^ (t + 1 + 1)) • (𝔤 (t + 1) 1) + (z * 2 ^ (t + 1 + 1)) • (𝔤 (t + 1) 2) := rfl
    rw [e, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hW0, hW1, hW2]
    simp only [smul_add, smul_sub, smul_neg, pow_succ_zsmul_tor300, pow_zsmul_tor310, add_zero,
      sub_zero, neg_zero]
    simp only [tor300]
    module
  have hx0p1 : 2 ∣ -p1 + r2 - r0 ∧ 2 ∣ p1 + 2 * r1 - x0 + 2 * x1 := by
    have h := hUW (𝔤 (t + 1) 1)
    rw [hW1, hU1'] at h
    simp only [map_add, map_sub, map_neg, map_zsmul] at h
    rw [hU1', hUt, hUt, hV2', hVt] at h
    simp only [map_add, map_zsmul] at h
    rw [hW0c, hW1, hW2, hWt, hWt] at h
    have key : tor300 (t + 1)
        (-x0 - (p0 - 4 * p2) - (r0 - 4 * r2) + 2 * (p0 - 4 * p2) + 2 * (r0 - 4 * r2) -
          (p0 - 4 * p2) - ((r0) - 4 * (r2)) -
          ((-3 * x0 + 4 * x1 + 4 * x2) - 4 * (-x0 + 2 * x1 + x2)))
        (-x1 - (p1 - p2) - (r1 - r2) + 2 * (-p2) + 2 * (-r2) - (-p2) -
          (r0 - r1 - 2 * r2) -
          ((-3 * x0 + 4 * x1 + 4 * x2) - (-x0 + x1 + 2 * x2) - 2 * (-x0 + 2 * x1 + x2)))
        (-x2 - (-p2) - (-r2) + 2 * (p1 - p2) + 2 * (r1 - r2) - (p1 - p2) - (-r2) -
          (-(-x0 + 2 * x1 + x2))) =
        tor300 (t + 1) 0 0 0 := by
      simp only [tor300] at h ⊢
      linear_combination (norm := module) h
    rw [tor300_eq_iff] at key
    omega
  refine ⟨x2, p2, ?_, ?_, ?_⟩
  · rw [hU1']
    congr 1
    apply tor300_congr <;> omega
  · rw [hV1']
    congr 1
    apply tor300_congr <;> omega
  · rw [hV2']
    congr 1
    apply tor300_congr <;> omega


theorem images310 {t : ℕ}
    (V W U R : Torus (Type100.k (t + 1 + 1)) →+ Torus (Type100.k (t + 1 + 1)))
    (hrels : SigmaFourRels V W U R)
    (hR0 : R (𝔤 (t + 1) 0) = (𝔤 (t + 1) 0)) (hR1 : R (𝔤 (t + 1) 1) = (𝔤 (t + 1) 2))
    (hR2 : R (𝔤 (t + 1) 2) =
      (-2 : ℤ) • (𝔤 (t + 1) 0) + (-1 : ℤ) • (𝔤 (t + 1) 1) + (-1 : ℤ) • (𝔤 (t + 1) 2))
    (hU0 : U (𝔤 (t + 1) 0) = (𝔤 (t + 1) 0) + tor300 (t + 1) 1 0 0)
    (hU1 : (2 : ℤ) • U (𝔤 (t + 1) 1) = (2 : ℤ) • (𝔤 (t + 1) 2))
    (hV0 : V (𝔤 (t + 1) 0) = (-3 : ℤ) • (𝔤 (t + 1) 0) + (-2 : ℤ) • (𝔤 (t + 1) 1) +
      (-2 : ℤ) • (𝔤 (t + 1) 2) + tor300 (t + 1) 0 1 0)
    (hV1 : (2 : ℤ) • V (𝔤 (t + 1) 1) =
      (4 : ℤ) • (𝔤 (t + 1) 0) + (2 : ℤ) • (𝔤 (t + 1) 1) + (4 : ℤ) • (𝔤 (t + 1) 2))
    (hV2 : (2 : ℤ) • V (𝔤 (t + 1) 2) =
      (4 : ℤ) • (𝔤 (t + 1) 0) + (4 : ℤ) • (𝔤 (t + 1) 1) + (2 : ℤ) • (𝔤 (t + 1) 2))
    (hUe : U (𝔤 (t + 1) 1) = (𝔤 (t + 1) 2)) :
    (∀ j : Fin 3, V (𝔤 (t + 1) j) = (Type110.action t).φuv (𝔤 (t + 1) j) ∧
      W (𝔤 (t + 1) j) = (Type110.action t).φt (𝔤 (t + 1) j) ∧
      U (𝔤 (t + 1) j) = (Type110.action t).φu (𝔤 (t + 1) j) ∧
      R (𝔤 (t + 1) j) = (Type110.action t).φρ (𝔤 (t + 1) j)) ∨
    (∀ j : Fin 3, V (𝔤 (t + 1) j) = (Type111.action t).φuv (𝔤 (t + 1) j) ∧
      W (𝔤 (t + 1) j) = (Type111.action t).φt (𝔤 (t + 1) j) ∧
      U (𝔤 (t + 1) j) = (Type111.action t).φu (𝔤 (t + 1) j) ∧
      R (𝔤 (t + 1) j) = (Type111.action t).φρ (𝔤 (t + 1) j)) := by
  obtain ⟨-, q, -, hV1e, hV2e⟩ := lifts310 V W U R hrels hR0 hR1 hR2 hU0 hU1 hV0 hV1 hV2
  have hRRR : ∀ w, R (R (R w)) = w := fun w => DFunLike.congr_fun hrels.rho_cube w
  have hUU : ∀ w, U (U w) = w := fun w => DFunLike.congr_fun hrels.u_sq w
  have hRURU : ∀ w, R (U (R (U w))) = w := fun w => DFunLike.congr_fun hrels.u_rho w
  have hRV : ∀ w, R (V w) = W (R w) := fun w => DFunLike.congr_fun hrels.uv_rho w
  have hUR : ∀ w, U (R w) = R (R (U w)) := by
    intro w
    have h := hRURU (U w)
    rw [hUU] at h
    have h2 : R (R (R (U (R w)))) = R (R (U w)) := congrArg (fun v => R (R v)) h
    rw [hRRR] at h2
    exact h2
  have hRt : ∀ x y z : ℤ, R (tor300 (t + 1) x y z) =
      tor300 (t + 1) (x - 4 * z) (-z) (y - z) := by
    intro x y z
    simp only [tor300, map_add, map_zsmul, hR0, hR1, hR2]
    module
  have hRRf : R (R (𝔤 (t + 1) 2)) = (𝔤 (t + 1) 1) := by
    rw [hR2]
    simp only [map_add, map_zsmul, hR0, hR1, hR2]
    module
  have hU2e : U (𝔤 (t + 1) 2) = (𝔤 (t + 1) 1) := by rw [← hR1, hUR, hUe, hRRf]
  have hV0c' : (-2 : ℤ) • V (𝔤 (t + 1) 0) = (-2 : ℤ) • ((-3 : ℤ) • (𝔤 (t + 1) 0) +
      (-2 : ℤ) • (𝔤 (t + 1) 1) + (-2 : ℤ) • (𝔤 (t + 1) 2)) := by
    rw [hV0, smul_add _ _ (tor300 (t + 1) 0 1 0), neg_two_zsmul_tor310, add_zero]
  have hW0 : W (𝔤 (t + 1) 0) = (𝔤 (t + 1) 0) + (2 : ℤ) • (𝔤 (t + 1) 1) +
      tor300 (t + 1) 0 0 1 := by
    have h := hRV (𝔤 (t + 1) 0)
    rw [hR0, hV0] at h
    rw [← h]
    simp only [map_add, map_zsmul, hR0, hR1, hR2, hRt]
    simp only [tor300]
    module
  have hW2 : W (𝔤 (t + 1) 2) = (-2 : ℤ) • (𝔤 (t + 1) 0) + (-2 : ℤ) • (𝔤 (t + 1) 1) +
      (-1 : ℤ) • (𝔤 (t + 1) 2) + tor300 (t + 1) (0 - 4 * q) (-q) (0 - q) := by
    have h := hRV (𝔤 (t + 1) 1)
    rw [hR1, hV1e] at h
    rw [← h]
    simp only [map_add, map_zsmul, hR0, hR1, hR2, hRt]
    module
  have hW1 : W (𝔤 (t + 1) 1) = -(𝔤 (t + 1) 1) - tor300 (t + 1) (0 - 4 * q) (-q) (0 - q) -
      tor300 (t + 1) (0 - 4 * 0) (-0) (q - 0) := by
    have h := hRV (R (𝔤 (t + 1) 2))
    rw [hRRf] at h
    rw [← h, hR2]
    simp only [map_add, map_zsmul, hV0c', hV1e, hV2e]
    simp only [map_add, map_zsmul, hR0, hR1, hR2, hRt]
    module
  have a_uv0 : (Type110.action t).φuv (𝔤 (t + 1) 0) = (-3 : ℤ) • (𝔤 (t + 1) 0) +
      (4 * (2 ^ t) - 2 : ℤ) • (𝔤 (t + 1) 1) + (-2 : ℤ) • (𝔤 (t + 1) 2) := Type110.uv_c t
  have a_uv1 : (Type110.action t).φuv (𝔤 (t + 1) 1) = (2 : ℤ) • (𝔤 (t + 1) 0) +
      (1 : ℤ) • (𝔤 (t + 1) 1) + (2 : ℤ) • (𝔤 (t + 1) 2) := Type110.uv_a t
  have a_uv2 : (Type110.action t).φuv (𝔤 (t + 1) 2) = (2 - 16 * (2 ^ t) : ℤ) • (𝔤 (t + 1) 0) +
      (2 - 8 * (2 ^ t) : ℤ) • (𝔤 (t + 1) 1) + (1 - 8 * (2 ^ t) : ℤ) • (𝔤 (t + 1) 2) :=
    Type110.uv_b t
  have a_t0 : (Type110.action t).φt (𝔤 (t + 1) 0) = (1 : ℤ) • (𝔤 (t + 1) 0) +
      (2 : ℤ) • (𝔤 (t + 1) 1) + (4 * (2 ^ t) : ℤ) • (𝔤 (t + 1) 2) := Type110.t_c t
  have a_t1 : (Type110.action t).φt (𝔤 (t + 1) 1) = (-1 : ℤ) • (𝔤 (t + 1) 1) := Type110.t_a t
  have a_t2 : (Type110.action t).φt (𝔤 (t + 1) 2) = (-2 : ℤ) • (𝔤 (t + 1) 0) +
      (-2 : ℤ) • (𝔤 (t + 1) 1) + (-1 : ℤ) • (𝔤 (t + 1) 2) := Type110.t_b t
  have a_u0 : (Type110.action t).φu (𝔤 (t + 1) 0) = (2 * (2 ^ t) + 1 : ℤ) • (𝔤 (t + 1) 0) :=
    Type110.u_c t
  have a_u1 : (Type110.action t).φu (𝔤 (t + 1) 1) = (1 : ℤ) • (𝔤 (t + 1) 2) := Type110.u_a t
  have a_u2 : (Type110.action t).φu (𝔤 (t + 1) 2) = (1 : ℤ) • (𝔤 (t + 1) 1) := Type110.u_b t
  have a_r0 : (Type110.action t).φρ (𝔤 (t + 1) 0) = (1 : ℤ) • (𝔤 (t + 1) 0) := Type110.rho_c t
  have a_r1 : (Type110.action t).φρ (𝔤 (t + 1) 1) = (1 : ℤ) • (𝔤 (t + 1) 2) := Type110.rho_a t
  have a_r2 : (Type110.action t).φρ (𝔤 (t + 1) 2) = (-2 : ℤ) • (𝔤 (t + 1) 0) +
      (-1 : ℤ) • (𝔤 (t + 1) 1) + (-1 : ℤ) • (𝔤 (t + 1) 2) := Type110.rho_b t
  have b_uv0 : (Type111.action t).φuv (𝔤 (t + 1) 0) = (-3 : ℤ) • (𝔤 (t + 1) 0) +
      (4 * (2 ^ t) - 2 : ℤ) • (𝔤 (t + 1) 1) + (-2 : ℤ) • (𝔤 (t + 1) 2) := Type111.uv_c t
  have b_uv1 : (Type111.action t).φuv (𝔤 (t + 1) 1) = (2 : ℤ) • (𝔤 (t + 1) 0) +
      (1 : ℤ) • (𝔤 (t + 1) 1) + (4 * (2 ^ t) + 2 : ℤ) • (𝔤 (t + 1) 2) := Type111.uv_a t
  have b_uv2 : (Type111.action t).φuv (𝔤 (t + 1) 2) = (2 - 16 * (2 ^ t) : ℤ) • (𝔤 (t + 1) 0) +
      (16 * (2 ^ t) ^ 2 + 4 * (2 ^ t) + 2 : ℤ) • (𝔤 (t + 1) 1) +
      (1 - 8 * (2 ^ t) : ℤ) • (𝔤 (t + 1) 2) := Type111.uv_b t
  have b_t0 : (Type111.action t).φt (𝔤 (t + 1) 0) = (1 : ℤ) • (𝔤 (t + 1) 0) +
      (2 : ℤ) • (𝔤 (t + 1) 1) + (4 * (2 ^ t) : ℤ) • (𝔤 (t + 1) 2) := Type111.t_c t
  have b_t1 : (Type111.action t).φt (𝔤 (t + 1) 1) = (4 * (2 ^ t) - 1 : ℤ) • (𝔤 (t + 1) 1) :=
    Type111.t_a t
  have b_t2 : (Type111.action t).φt (𝔤 (t + 1) 2) = (-8 * (2 ^ t) - 2 : ℤ) • (𝔤 (t + 1) 0) +
      (-4 * (2 ^ t) - 2 : ℤ) • (𝔤 (t + 1) 1) + (-4 * (2 ^ t) - 1 : ℤ) • (𝔤 (t + 1) 2) :=
    Type111.t_b t
  have b_u0 : (Type111.action t).φu (𝔤 (t + 1) 0) = (2 * (2 ^ t) + 1 : ℤ) • (𝔤 (t + 1) 0) :=
    Type111.u_c t
  have b_u1 : (Type111.action t).φu (𝔤 (t + 1) 1) = (1 : ℤ) • (𝔤 (t + 1) 2) := Type111.u_a t
  have b_u2 : (Type111.action t).φu (𝔤 (t + 1) 2) = (1 : ℤ) • (𝔤 (t + 1) 1) := Type111.u_b t
  have b_r0 : (Type111.action t).φρ (𝔤 (t + 1) 0) = (1 : ℤ) • (𝔤 (t + 1) 0) := Type111.rho_c t
  have b_r1 : (Type111.action t).φρ (𝔤 (t + 1) 1) = (1 : ℤ) • (𝔤 (t + 1) 2) := Type111.rho_a t
  have b_r2 : (Type111.action t).φρ (𝔤 (t + 1) 2) = (-2 : ℤ) • (𝔤 (t + 1) 0) +
      (-1 : ℤ) • (𝔤 (t + 1) 1) + (-1 : ℤ) • (𝔤 (t + 1) 2) := Type111.rho_b t
  have hV0' : V (𝔤 (t + 1) 0) = (-3 : ℤ) • (𝔤 (t + 1) 0) +
      (4 * (2 ^ t) - 2 : ℤ) • (𝔤 (t + 1) 1) + (-2 : ℤ) • (𝔤 (t + 1) 2) := by
    rw [hV0]
    simp only [tor300]
    rw [pow_succ, pow_succ]
    module
  have hW0' : W (𝔤 (t + 1) 0) = (1 : ℤ) • (𝔤 (t + 1) 0) +
      (2 : ℤ) • (𝔤 (t + 1) 1) + (4 * (2 ^ t) : ℤ) • (𝔤 (t + 1) 2) := by
    rw [hW0]
    simp only [tor300]
    rw [pow_succ, pow_succ]
    module
  have hU0' : U (𝔤 (t + 1) 0) = (2 * (2 ^ t) + 1 : ℤ) • (𝔤 (t + 1) 0) := by
    rw [hU0]
    simp only [tor300]
    rw [pow_succ]
    module
  have c0 : V (𝔤 (t + 1) 0) = (Type110.action t).φuv (𝔤 (t + 1) 0) ∧
      W (𝔤 (t + 1) 0) = (Type110.action t).φt (𝔤 (t + 1) 0) ∧
      U (𝔤 (t + 1) 0) = (Type110.action t).φu (𝔤 (t + 1) 0) ∧
      R (𝔤 (t + 1) 0) = (Type110.action t).φρ (𝔤 (t + 1) 0) :=
    ⟨hV0'.trans a_uv0.symm, hW0'.trans a_t0.symm, hU0'.trans a_u0.symm,
      hR0.trans (by rw [a_r0]; module)⟩
  have d0 : V (𝔤 (t + 1) 0) = (Type111.action t).φuv (𝔤 (t + 1) 0) ∧
      W (𝔤 (t + 1) 0) = (Type111.action t).φt (𝔤 (t + 1) 0) ∧
      U (𝔤 (t + 1) 0) = (Type111.action t).φu (𝔤 (t + 1) 0) ∧
      R (𝔤 (t + 1) 0) = (Type111.action t).φρ (𝔤 (t + 1) 0) :=
    ⟨hV0'.trans b_uv0.symm, hW0'.trans b_t0.symm, hU0'.trans b_u0.symm,
      hR0.trans (by rw [b_r0]; module)⟩
  obtain ⟨u, rfl | rfl⟩ := Int.even_or_odd' q
  ·
    left
    have h1 : V (𝔤 (t + 1) 1) = (Type110.action t).φuv (𝔤 (t + 1) 1) ∧
        W (𝔤 (t + 1) 1) = (Type110.action t).φt (𝔤 (t + 1) 1) ∧
        U (𝔤 (t + 1) 1) = (Type110.action t).φu (𝔤 (t + 1) 1) ∧
        R (𝔤 (t + 1) 1) = (Type110.action t).φρ (𝔤 (t + 1) 1) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hV1e, a_uv1]
        calc _ = (2 : ℤ) • (𝔤 (t + 1) 0) + (1 : ℤ) • (𝔤 (t + 1) 1) +
            (2 + 2 * u * 2 ^ (t + 1 + 1)) • (𝔤 (t + 1) 2) := by
              simp only [tor300]; module
          _ = _ := by
              apply zsmul_gens_eq_of_dvd
              · simp
              · simp
              · change (2 : ℤ) ^ (t + 1 + 1 + 1) ∣ _
                exact ⟨-u, by ring⟩
      · rw [hW1, a_t1]
        calc _ = (4 * (2 * u) * 2 ^ (t + 1)) • (𝔤 (t + 1) 0) +
            (-1 + 2 * u * 2 ^ (t + 1 + 1)) • (𝔤 (t + 1) 1) + (0 : ℤ) • (𝔤 (t + 1) 2) := by
              simp only [tor300]; module
          _ = (0 : ℤ) • (𝔤 (t + 1) 0) + (-1 : ℤ) • (𝔤 (t + 1) 1) + (0 : ℤ) • (𝔤 (t + 1) 2) := by
              apply zsmul_gens_eq_of_dvd
              · change (2 : ℤ) ^ (t + 1 + 1) ∣ _
                exact ⟨-(4 * u), by ring⟩
              · change (2 : ℤ) ^ (t + 1 + 1 + 1) ∣ _
                exact ⟨-u, by ring⟩
              · simp
          _ = _ := by module
      · rw [hUe, a_u1]; module
      · rw [hR1, a_r1]; module
    have h2 : V (𝔤 (t + 1) 2) = (Type110.action t).φuv (𝔤 (t + 1) 2) ∧
        W (𝔤 (t + 1) 2) = (Type110.action t).φt (𝔤 (t + 1) 2) ∧
        U (𝔤 (t + 1) 2) = (Type110.action t).φu (𝔤 (t + 1) 2) ∧
        R (𝔤 (t + 1) 2) = (Type110.action t).φρ (𝔤 (t + 1) 2) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hV2e, a_uv2]
        calc _ = (2 : ℤ) • (𝔤 (t + 1) 0) + (2 + 2 * u * 2 ^ (t + 1 + 1)) • (𝔤 (t + 1) 1) +
            (1 : ℤ) • (𝔤 (t + 1) 2) := by
              simp only [tor300]; module
          _ = _ := by
              apply zsmul_gens_eq_of_dvd
              · change (2 : ℤ) ^ (t + 1 + 1) ∣ _
                exact ⟨-4, by ring⟩
              · change (2 : ℤ) ^ (t + 1 + 1 + 1) ∣ _
                exact ⟨-1 - u, by ring⟩
              · change (2 : ℤ) ^ (t + 1 + 1 + 1) ∣ _
                exact ⟨-1, by ring⟩
      · rw [hW2, a_t2]
        calc _ = (-2 - 4 * (2 * u) * 2 ^ (t + 1)) • (𝔤 (t + 1) 0) +
            (-2 - 2 * u * 2 ^ (t + 1 + 1)) • (𝔤 (t + 1) 1) +
              (-1 - 2 * u * 2 ^ (t + 1 + 1)) • (𝔤 (t + 1) 2) := by
              simp only [tor300]; module
          _ = _ := by
              apply zsmul_gens_eq_of_dvd
              · change (2 : ℤ) ^ (t + 1 + 1) ∣ _
                exact ⟨4 * u, by ring⟩
              · change (2 : ℤ) ^ (t + 1 + 1 + 1) ∣ _
                exact ⟨u, by ring⟩
              · change (2 : ℤ) ^ (t + 1 + 1 + 1) ∣ _
                exact ⟨u, by ring⟩
      · rw [hU2e, a_u2]; module
      · rw [hR2, a_r2]
    intro j
    fin_cases j
    exacts [c0, h1, h2]
  ·
    right
    have h1 : V (𝔤 (t + 1) 1) = (Type111.action t).φuv (𝔤 (t + 1) 1) ∧
        W (𝔤 (t + 1) 1) = (Type111.action t).φt (𝔤 (t + 1) 1) ∧
        U (𝔤 (t + 1) 1) = (Type111.action t).φu (𝔤 (t + 1) 1) ∧
        R (𝔤 (t + 1) 1) = (Type111.action t).φρ (𝔤 (t + 1) 1) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hV1e, b_uv1]
        calc _ = (2 : ℤ) • (𝔤 (t + 1) 0) + (1 : ℤ) • (𝔤 (t + 1) 1) +
            (2 + (2 * u + 1) * 2 ^ (t + 1 + 1)) • (𝔤 (t + 1) 2) := by
              simp only [tor300]; module
          _ = _ := by
              apply zsmul_gens_eq_of_dvd
              · simp
              · simp
              · change (2 : ℤ) ^ (t + 1 + 1 + 1) ∣ _
                exact ⟨-u, by ring⟩
      · rw [hW1, b_t1]
        calc _ = (4 * (2 * u + 1) * 2 ^ (t + 1)) • (𝔤 (t + 1) 0) +
            (-1 + (2 * u + 1) * 2 ^ (t + 1 + 1)) • (𝔤 (t + 1) 1) +
              (0 : ℤ) • (𝔤 (t + 1) 2) := by
              simp only [tor300]; module
          _ = (0 : ℤ) • (𝔤 (t + 1) 0) + (4 * (2 ^ t) - 1 : ℤ) • (𝔤 (t + 1) 1) +
              (0 : ℤ) • (𝔤 (t + 1) 2) := by
              apply zsmul_gens_eq_of_dvd
              · change (2 : ℤ) ^ (t + 1 + 1) ∣ _
                exact ⟨-(4 * u + 2), by ring⟩
              · change (2 : ℤ) ^ (t + 1 + 1 + 1) ∣ _
                exact ⟨-u, by ring⟩
              · simp
          _ = _ := by module
      · rw [hUe, b_u1]; module
      · rw [hR1, b_r1]; module
    have h2 : V (𝔤 (t + 1) 2) = (Type111.action t).φuv (𝔤 (t + 1) 2) ∧
        W (𝔤 (t + 1) 2) = (Type111.action t).φt (𝔤 (t + 1) 2) ∧
        U (𝔤 (t + 1) 2) = (Type111.action t).φu (𝔤 (t + 1) 2) ∧
        R (𝔤 (t + 1) 2) = (Type111.action t).φρ (𝔤 (t + 1) 2) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hV2e, b_uv2]
        calc _ = (2 : ℤ) • (𝔤 (t + 1) 0) + (2 + (2 * u + 1) * 2 ^ (t + 1 + 1)) • (𝔤 (t + 1) 1) +
            (1 : ℤ) • (𝔤 (t + 1) 2) := by
              simp only [tor300]; module
          _ = _ := by
              apply zsmul_gens_eq_of_dvd
              · change (2 : ℤ) ^ (t + 1 + 1) ∣ _
                exact ⟨-4, by ring⟩
              · change (2 : ℤ) ^ (t + 1 + 1 + 1) ∣ _
                exact ⟨2 * 2 ^ t - u, by ring⟩
              · change (2 : ℤ) ^ (t + 1 + 1 + 1) ∣ _
                exact ⟨-1, by ring⟩
      · rw [hW2, b_t2]
        calc _ = (-2 - 4 * (2 * u + 1) * 2 ^ (t + 1)) • (𝔤 (t + 1) 0) +
            (-2 - (2 * u + 1) * 2 ^ (t + 1 + 1)) • (𝔤 (t + 1) 1) +
              (-1 - (2 * u + 1) * 2 ^ (t + 1 + 1)) • (𝔤 (t + 1) 2) := by
              simp only [tor300]; module
          _ = _ := by
              apply zsmul_gens_eq_of_dvd
              · change (2 : ℤ) ^ (t + 1 + 1) ∣ _
                exact ⟨4 * u, by ring⟩
              · change (2 : ℤ) ^ (t + 1 + 1 + 1) ∣ _
                exact ⟨u, by ring⟩
              · change (2 : ℤ) ^ (t + 1 + 1 + 1) ∣ _
                exact ⟨u, by ring⟩
      · rw [hU2e, b_u2]; module
      · rw [hR2, b_r2]
    intro j
    fin_cases j
    exacts [d0, h1, h2]

theorem U_tor310 {t : ℕ} (U : Torus (Type100.k (t + 1 + 1)) →+ Torus (Type100.k (t + 1 + 1)))
    (hU0 : U (𝔤 (t + 1) 0) = (𝔤 (t + 1) 0) + tor300 (t + 1) 1 0 0)
    (hU1 : (2 : ℤ) • U (𝔤 (t + 1) 1) = (2 : ℤ) • (𝔤 (t + 1) 2))
    (hU2 : (2 : ℤ) • U (𝔤 (t + 1) 2) = (2 : ℤ) • (𝔤 (t + 1) 1)) (x y z : ℤ) :
    U (tor300 (t + 1) x y z) = tor300 (t + 1) x z y := by
  have e : tor300 (t + 1) x y z = (x * 2 ^ (t + 1)) • (𝔤 (t + 1) 0) +
      (y * 2 ^ (t + 1 + 1)) • (𝔤 (t + 1) 1) + (z * 2 ^ (t + 1 + 1)) • (𝔤 (t + 1) 2) := rfl
  have e1 : (y * 2 ^ (t + 1 + 1)) • U (𝔤 (t + 1) 1) =
      (y * 2 ^ (t + 1)) • ((2 : ℤ) • U (𝔤 (t + 1) 1)) := by
    rw [smul_smul, show y * 2 ^ (t + 1) * 2 = y * 2 ^ (t + 1 + 1) by ring]
  have e2 : (z * 2 ^ (t + 1 + 1)) • U (𝔤 (t + 1) 2) =
      (z * 2 ^ (t + 1)) • ((2 : ℤ) • U (𝔤 (t + 1) 2)) := by
    rw [smul_smul, show z * 2 ^ (t + 1) * 2 = z * 2 ^ (t + 1 + 1) by ring]
  rw [e, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hU0, e1, e2, hU1, hU2, smul_add,
    pow_zsmul_tor310, add_zero]
  simp only [tor300]
  module

end CFSG.CGT.Stroth77
