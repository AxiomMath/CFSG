module

public import CFSG.CGT.Stroth77.Extension24Basic
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CGT.Stroth77.Extension22FourC4
public import CFSG.CGT.Stroth77.TorusCard
public import CFSG.Foundations

local notation "𝔤" s:max j:max => CFSG.CGT.Stroth77.gen (CFSG.CGT.Stroth77.Type100.k (s + 1)) j

public section

namespace CFSG.CGT.Stroth77

@[expose] def tor300 (s : ℕ) (x y z : ℤ) : Torus (Type100.k (s + 1)) :=
  (x * 2 ^ s) • (𝔤 s 0) + (y * 2 ^ (s + 1)) • (𝔤 s 1) + (z * 2 ^ (s + 1)) • (𝔤 s 2)

theorem tor300_eq_iff {s : ℕ} {x y z x' y' z' : ℤ} :
    tor300 s x y z = tor300 s x' y' z' ↔ 2 ∣ x' - x ∧ 2 ∣ y' - y ∧ 2 ∣ z' - z := by
  have hs : (2 : ℤ) ^ s ≠ 0 := pow_ne_zero _ two_ne_zero
  have hs1 : (2 : ℤ) ^ (s + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  have e0 : x' * 2 ^ s - x * 2 ^ s = 2 ^ s * (x' - x) := by ring
  have e1 : y' * 2 ^ (s + 1) - y * 2 ^ (s + 1) = 2 ^ (s + 1) * (y' - y) := by ring
  have e2 : z' * 2 ^ (s + 1) - z * 2 ^ (s + 1) = 2 ^ (s + 1) * (z' - z) := by ring
  constructor
  · intro h
    obtain ⟨h0, h1, h2⟩ := zsmul_gens_dvd_of_eq h
    change (2 : ℤ) ^ (s + 1) ∣ _ at h0
    change (2 : ℤ) ^ (s + 1 + 1) ∣ _ at h1
    change (2 : ℤ) ^ (s + 1 + 1) ∣ _ at h2
    rw [e0, pow_succ] at h0
    rw [e1, pow_succ (2 : ℤ) (s + 1)] at h1
    rw [e2, pow_succ (2 : ℤ) (s + 1)] at h2
    exact ⟨(mul_dvd_mul_iff_left hs).mp h0, (mul_dvd_mul_iff_left hs1).mp h1,
      (mul_dvd_mul_iff_left hs1).mp h2⟩
  · rintro ⟨h0, h1, h2⟩
    apply zsmul_gens_eq_of_dvd
    · change (2 : ℤ) ^ (s + 1) ∣ _
      rw [e0, pow_succ]
      exact mul_dvd_mul_left _ h0
    · change (2 : ℤ) ^ (s + 1 + 1) ∣ _
      rw [e1, pow_succ (2 : ℤ) (s + 1)]
      exact mul_dvd_mul_left _ h1
    · change (2 : ℤ) ^ (s + 1 + 1) ∣ _
      rw [e2, pow_succ (2 : ℤ) (s + 1)]
      exact mul_dvd_mul_left _ h2

theorem tor300_congr {s : ℕ} {x y z x' y' z' : ℤ} (h0 : 2 ∣ x' - x) (h1 : 2 ∣ y' - y)
    (h2 : 2 ∣ z' - z) : tor300 s x y z = tor300 s x' y' z' :=
  tor300_eq_iff.mpr ⟨h0, h1, h2⟩

theorem tor300_zero {s : ℕ} : tor300 s 0 0 0 = 0 := by
  simp [tor300]

theorem tor300_add {s : ℕ} (x y z x' y' z' : ℤ) :
    tor300 s x y z + tor300 s x' y' z' = tor300 s (x + x') (y + y') (z + z') := by
  simp only [tor300]
  module

theorem two_zsmul_tor300 {s : ℕ} (x y z : ℤ) : (2 : ℤ) • tor300 s x y z = 0 := by
  have e : (2 : ℤ) • tor300 s x y z = tor300 s (2 * x) (2 * y) (2 * z) := by
    simp only [tor300]
    module
  rw [e, ← tor300_zero]
  exact tor300_congr ⟨-x, by ring⟩ ⟨-y, by ring⟩ ⟨-z, by ring⟩

theorem pow_succ_zsmul_tor300 {s : ℕ} (m x y z : ℤ) :
    (m * 2 ^ (s + 1)) • tor300 s x y z = 0 := by
  rw [show m * 2 ^ (s + 1) = (m * 2 ^ s) * 2 by ring, mul_smul, two_zsmul_tor300, smul_zero]

theorem exists_tor300 {s : ℕ} {w : Torus (Type100.k (s + 1))} (hw : (2 : ℤ) • w = 0) :
    ∃ x y z : ℤ, w = tor300 s x y z := by
  obtain ⟨p, q, r, rfl⟩ := torus_eq_zsmul_gens (Type100.k (s + 1)) w
  have h : (2 * p) • (𝔤 s 0) + (2 * q) • (𝔤 s 1) + (2 * r) • (𝔤 s 2) = (0 : ℤ) • (𝔤 s 0) +
      (0 : ℤ) • (𝔤 s 1) +
      (0 : ℤ) • (𝔤 s 2) := by
    rw [zero_smul, zero_smul, zero_smul, add_zero, add_zero, ← hw]
    module
  obtain ⟨h0, h1, h2⟩ := zsmul_gens_dvd_of_eq h
  change (2 : ℤ) ^ (s + 1) ∣ _ at h0
  change (2 : ℤ) ^ (s + 1 + 1) ∣ _ at h1
  change (2 : ℤ) ^ (s + 1 + 1) ∣ _ at h2
  have two_ne : (2 : ℤ) ≠ 0 := two_ne_zero
  rw [show (0 : ℤ) - 2 * p = 2 * (-p) by ring, pow_succ, mul_comm _ (2 : ℤ)] at h0
  rw [show (0 : ℤ) - 2 * q = 2 * (-q) by ring, pow_succ (2 : ℤ) (s + 1),
    mul_comm _ (2 : ℤ)] at h1
  rw [show (0 : ℤ) - 2 * r = 2 * (-r) by ring, pow_succ (2 : ℤ) (s + 1),
    mul_comm _ (2 : ℤ)] at h2
  obtain ⟨x, hx⟩ := dvd_neg.mp ((mul_dvd_mul_iff_left two_ne).mp h0)
  obtain ⟨y, hy⟩ := dvd_neg.mp ((mul_dvd_mul_iff_left two_ne).mp h1)
  obtain ⟨z, hz⟩ := dvd_neg.mp ((mul_dvd_mul_iff_left two_ne).mp h2)
  refine ⟨x, y, z, ?_⟩
  rw [hx, hy, hz]
  simp only [tor300]
  module

theorem lifts300 {s : ℕ} (V W U R : Torus (Type100.k (s + 1)) →+ Torus (Type100.k (s + 1)))
    (hrels : SigmaFourRels V W U R)
    (hR0 : R (𝔤 s 0) = (𝔤 s 0)) (hR1 : R (𝔤 s 1) = (𝔤 s 2))
    (hR2 : R (𝔤 s 2) = (-2 : ℤ) • (𝔤 s 0) + (-1 : ℤ) • (𝔤 s 1) + (-1 : ℤ) • (𝔤 s 2))
    (hU0 : U (𝔤 s 0) = (𝔤 s 0)) (hU1 : (2 : ℤ) • U (𝔤 s 1) = (2 : ℤ) • (𝔤 s 2))
    (hV0 : V (𝔤 s 0) = (-3 : ℤ) • (𝔤 s 0) + (-2 : ℤ) • (𝔤 s 1) + (-2 : ℤ) • (𝔤 s 2))
    (hV1 : (2 : ℤ) • V (𝔤 s 1) = (4 : ℤ) • (𝔤 s 0) + (2 : ℤ) • (𝔤 s 1) + (4 : ℤ) • (𝔤 s 2))
    (hV2 : (2 : ℤ) • V (𝔤 s 2) = (4 : ℤ) • (𝔤 s 0) + (4 : ℤ) • (𝔤 s 1) + (2 : ℤ) • (𝔤 s 2)) :
    ∃ x q : ℤ, U (𝔤 s 1) = (𝔤 s 2) + tor300 s 0 0 x ∧
      V (𝔤 s 1) = (2 : ℤ) • (𝔤 s 0) + (𝔤 s 1) + (2 : ℤ) • (𝔤 s 2) + tor300 s 0 0 q ∧
      V (𝔤 s 2) = (2 : ℤ) • (𝔤 s 0) + (2 : ℤ) • (𝔤 s 1) + (𝔤 s 2) + tor300 s 0 q 0 := by
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
  obtain ⟨x0, x1, x2, hν⟩ := exists_tor300 (s := s) (w := U (𝔤 s 1) - (𝔤 s 2))
    (by rw [smul_sub, hU1, sub_self])
  obtain ⟨p0, p1, p2, hω1⟩ := exists_tor300 (s := s)
    (w := V (𝔤 s 1) - ((2 : ℤ) • (𝔤 s 0) + (𝔤 s 1) + (2 : ℤ) • (𝔤 s 2)))
        (by rw [smul_sub, hV1]; module)
  obtain ⟨r0, r1, r2, hω2⟩ := exists_tor300 (s := s)
    (w := V (𝔤 s 2) - ((2 : ℤ) • (𝔤 s 0) + (2 : ℤ) • (𝔤 s 1) + (𝔤 s 2)))
        (by rw [smul_sub, hV2]; module)
  have hU1' : U (𝔤 s 1) = (𝔤 s 2) + tor300 s x0 x1 x2 := by rw [← hν]; abel
  have hV1' : V (𝔤 s 1) = (2 : ℤ) • (𝔤 s 0) + (𝔤 s 1) + (2 : ℤ) • (𝔤 s 2) + tor300 s p0 p1 p2 := by
    rw [← hω1]; abel
  have hV2' : V (𝔤 s 2) = (2 : ℤ) • (𝔤 s 0) + (2 : ℤ) • (𝔤 s 1) + (𝔤 s 2) + tor300 s r0 r1 r2 := by
    rw [← hω2]; abel
  have hRt : ∀ x y z : ℤ, R (tor300 s x y z) = tor300 s (x - 4 * z) (-z) (y - z) := by
    intro x y z
    simp only [tor300, map_add, map_zsmul, hR0, hR1, hR2]
    module
  have hRRf : R (R (𝔤 s 2)) = (𝔤 s 1) := by
    rw [hR2]
    simp only [map_add, map_zsmul, hR0, hR1, hR2]
    module
  have hU2' : U (𝔤 s 2) = (𝔤 s 1) + tor300 s (x0 - 4 * x2 - 4 * (x1 - x2)) (-(x1 - x2))
      (-x2 - (x1 - x2)) := by
    rw [← hR1, hUR, hU1', map_add, map_add, hRRf, hRt, hRt]
  have hUt : ∀ x y z : ℤ, U (tor300 s x y z) = tor300 s x z y := by
    intro x y z
    have e : tor300 s x y z =
        (x * 2 ^ s) • (𝔤 s 0) + (y * 2 ^ (s + 1)) • (𝔤 s 1) + (z * 2 ^ (s + 1)) • (𝔤 s 2) := rfl
    rw [e, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hU0, hU1', hU2']
    simp only [smul_add, pow_succ_zsmul_tor300, add_zero]
    simp only [tor300]
    module
  have hx1 : 2 ∣ x1 := by
    have h := hUU (𝔤 s 1)
    rw [hU1', map_add, hU2', hUt] at h
    have key : tor300 s ((x0 - 4 * x2 - 4 * (x1 - x2)) + x0) ((-(x1 - x2)) + x2)
        ((-x2 - (x1 - x2)) + x1) = tor300 s 0 0 0 := by
      simp only [tor300] at h ⊢
      linear_combination (norm := module) h
    rw [tor300_eq_iff] at key
    omega
  have hVt : ∀ x y z : ℤ, V (tor300 s x y z) =
      tor300 s (-3 * x + 4 * y + 4 * z) (-x + y + 2 * z) (-x + 2 * y + z) := by
    intro x y z
    have e : tor300 s x y z =
        (x * 2 ^ s) • (𝔤 s 0) + (y * 2 ^ (s + 1)) • (𝔤 s 1) + (z * 2 ^ (s + 1)) • (𝔤 s 2) := rfl
    rw [e, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hV0, hV1', hV2']
    simp only [smul_add, pow_succ_zsmul_tor300, add_zero]
    simp only [tor300]
    module
  have hp0 : 2 ∣ p0 := by
    have h := hVV (𝔤 s 1)
    rw [hV1'] at h
    simp only [map_add, map_zsmul] at h
    rw [hV0, hV1', hV2', hVt] at h
    have key : tor300 s (p0 + 2 * r0 + (-3 * p0 + 4 * p1 + 4 * p2))
        (p1 + 2 * r1 + (-p0 + p1 + 2 * p2)) (p2 + 2 * r2 + (-p0 + 2 * p1 + p2)) =
        tor300 s 0 0 0 := by
      simp only [tor300] at h ⊢
      linear_combination (norm := module) h
    rw [tor300_eq_iff] at key
    omega
  have hr : 2 ∣ p0 - r0 ∧ 2 ∣ x0 + p2 - r1 ∧ 2 ∣ x0 + p1 - r2 := by
    have h := hUV (𝔤 s 1)
    rw [hV1', hU1'] at h
    simp only [map_add, map_zsmul] at h
    rw [hU0, hU1', hU2', hUt, hV2', hVt] at h
    have key : tor300 s (x0 + 2 * (x0 - 4 * x2 - 4 * (x1 - x2)) + p0 - r0 -
          (-3 * x0 + 4 * x1 + 4 * x2))
        (x1 + 2 * (-(x1 - x2)) + p2 - r1 - (-x0 + x1 + 2 * x2))
        (x2 + 2 * (-x2 - (x1 - x2)) + p1 - r2 - (-x0 + 2 * x1 + x2)) = tor300 s 0 0 0 := by
      simp only [tor300] at h ⊢
      linear_combination (norm := module) h
    rw [tor300_eq_iff] at key
    omega
  have hW0 : W (𝔤 s 0) = (𝔤 s 0) + (2 : ℤ) • (𝔤 s 1) := by
    have h := hRV (𝔤 s 0)
    rw [hR0, hV0] at h
    rw [← h]
    simp only [map_add, map_zsmul, hR0, hR1, hR2]
    module
  have hW2 : W (𝔤 s 2) = (-2 : ℤ) • (𝔤 s 0) + (-2 : ℤ) • (𝔤 s 1) + (-1 : ℤ) • (𝔤 s 2) +
      tor300 s (p0 - 4 * p2) (-p2) (p1 - p2) := by
    have h := hRV (𝔤 s 1)
    rw [hR1, hV1'] at h
    rw [← h]
    simp only [map_add, map_zsmul, hR0, hR1, hR2, hRt]
    module
  have hW1 : W (𝔤 s 1) = -(𝔤 s 1) - tor300 s (p0 - 4 * p2) (-p2) (p1 - p2) -
      tor300 s (r0 - 4 * r2) (-r2) (r1 - r2) := by
    have h := hRV (R (𝔤 s 2))
    rw [hRRf] at h
    rw [← h, hR2]
    simp only [map_add, map_zsmul, hV0, hV1', hV2']
    simp only [map_add, map_zsmul, hR0, hR1, hR2, hRt]
    module
  have hWt : ∀ x y z : ℤ, W (tor300 s x y z) = tor300 s (x - 4 * z) (x - y - 2 * z) (-z) := by
    intro x y z
    have e : tor300 s x y z =
        (x * 2 ^ s) • (𝔤 s 0) + (y * 2 ^ (s + 1)) • (𝔤 s 1) + (z * 2 ^ (s + 1)) • (𝔤 s 2) := rfl
    rw [e, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hW0, hW1, hW2]
    simp only [smul_add, smul_sub, smul_neg, pow_succ_zsmul_tor300, add_zero, sub_zero,
      neg_zero]
    simp only [tor300]
    module
  have hx0p1 : 2 ∣ -p1 + r2 - r0 ∧ 2 ∣ p1 + 2 * r1 - x0 + 2 * x1 := by
    have h := hUW (𝔤 s 1)
    rw [hW1, hU1'] at h
    simp only [map_add, map_sub, map_neg, map_zsmul] at h
    rw [hU1', hUt, hUt, hV2', hVt] at h
    simp only [map_add, map_zsmul] at h
    rw [hW0, hW1, hW2, hWt, hWt] at h
    have key : tor300 s
        (-x0 - (p0 - 4 * p2) - (r0 - 4 * r2) + 2 * (p0 - 4 * p2) + 2 * (r0 - 4 * r2) -
          (p0 - 4 * p2) - ((r0) - 4 * (r2)) -
          ((-3 * x0 + 4 * x1 + 4 * x2) - 4 * (-x0 + 2 * x1 + x2)))
        (-x1 - (p1 - p2) - (r1 - r2) + 2 * (-p2) + 2 * (-r2) - (-p2) -
          (r0 - r1 - 2 * r2) -
          ((-3 * x0 + 4 * x1 + 4 * x2) - (-x0 + x1 + 2 * x2) - 2 * (-x0 + 2 * x1 + x2)))
        (-x2 - (-p2) - (-r2) + 2 * (p1 - p2) + 2 * (r1 - r2) - (p1 - p2) - (-r2) -
          (-(-x0 + 2 * x1 + x2))) =
        tor300 s 0 0 0 := by
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

theorem images300 {s : ℕ} (V W U R : Torus (Type100.k (s + 1)) →+ Torus (Type100.k (s + 1)))
    (hrels : SigmaFourRels V W U R)
    (hR0 : R (𝔤 s 0) = (𝔤 s 0)) (hR1 : R (𝔤 s 1) = (𝔤 s 2))
    (hR2 : R (𝔤 s 2) = (-2 : ℤ) • (𝔤 s 0) + (-1 : ℤ) • (𝔤 s 1) + (-1 : ℤ) • (𝔤 s 2))
    (hU0 : U (𝔤 s 0) = (𝔤 s 0)) (hU1 : (2 : ℤ) • U (𝔤 s 1) = (2 : ℤ) • (𝔤 s 2))
    (hV0 : V (𝔤 s 0) = (-3 : ℤ) • (𝔤 s 0) + (-2 : ℤ) • (𝔤 s 1) + (-2 : ℤ) • (𝔤 s 2))
    (hV1 : (2 : ℤ) • V (𝔤 s 1) = (4 : ℤ) • (𝔤 s 0) + (2 : ℤ) • (𝔤 s 1) + (4 : ℤ) • (𝔤 s 2))
    (hV2 : (2 : ℤ) • V (𝔤 s 2) = (4 : ℤ) • (𝔤 s 0) + (4 : ℤ) • (𝔤 s 1) + (2 : ℤ) • (𝔤 s 2))
    (hUe : U (𝔤 s 1) = (𝔤 s 2)) :
    (∀ j : Fin 3, V (𝔤 s j) = (Type100.action (s + 1)).φuv (𝔤 s j) ∧
      W (𝔤 s j) = (Type100.action (s + 1)).φt (𝔤 s j) ∧
      U (𝔤 s j) = (Type100.action (s + 1)).φu (𝔤 s j) ∧
      R (𝔤 s j) = (Type100.action (s + 1)).φρ (𝔤 s j)) ∨
    (∀ j : Fin 3, V (𝔤 s j) = (Type101.action s).φuv (𝔤 s j) ∧
      W (𝔤 s j) = (Type101.action s).φt (𝔤 s j) ∧
      U (𝔤 s j) = (Type101.action s).φu (𝔤 s j) ∧
      R (𝔤 s j) = (Type101.action s).φρ (𝔤 s j)) := by
  obtain ⟨-, q, -, hV1e, hV2e⟩ := lifts300 V W U R hrels hR0 hR1 hR2 hU0 hU1 hV0 hV1 hV2
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
  have hRt : ∀ x y z : ℤ, R (tor300 s x y z) = tor300 s (x - 4 * z) (-z) (y - z) := by
    intro x y z
    simp only [tor300, map_add, map_zsmul, hR0, hR1, hR2]
    module
  have hRRf : R (R (𝔤 s 2)) = (𝔤 s 1) := by
    rw [hR2]
    simp only [map_add, map_zsmul, hR0, hR1, hR2]
    module
  have hU2e : U (𝔤 s 2) = (𝔤 s 1) := by rw [← hR1, hUR, hUe, hRRf]
  have hW0 : W (𝔤 s 0) = (𝔤 s 0) + (2 : ℤ) • (𝔤 s 1) := by
    have h := hRV (𝔤 s 0)
    rw [hR0, hV0] at h
    rw [← h]
    simp only [map_add, map_zsmul, hR0, hR1, hR2]
    module
  have hW2 : W (𝔤 s 2) = (-2 : ℤ) • (𝔤 s 0) + (-2 : ℤ) • (𝔤 s 1) + (-1 : ℤ) • (𝔤 s 2) +
      tor300 s (0 - 4 * q) (-q) (0 - q) := by
    have h := hRV (𝔤 s 1)
    rw [hR1, hV1e] at h
    rw [← h]
    simp only [map_add, map_zsmul, hR0, hR1, hR2, hRt]
    module
  have hW1 : W (𝔤 s 1) = -(𝔤 s 1) - tor300 s (0 - 4 * q) (-q) (0 - q) -
      tor300 s (0 - 4 * 0) (-0) (q - 0) := by
    have h := hRV (R (𝔤 s 2))
    rw [hRRf] at h
    rw [← h, hR2]
    simp only [map_add, map_zsmul, hV0, hV1e, hV2e]
    simp only [map_add, map_zsmul, hR0, hR1, hR2, hRt]
    module
  have a_uv0 := Type100.uv_c (s + 1)
  have a_uv1 := Type100.uv_a (s + 1)
  have a_uv2 := Type100.uv_b (s + 1)
  have a_t0 := Type100.t_c (s + 1)
  have a_t1 := Type100.t_a (s + 1)
  have a_t2 := Type100.t_b (s + 1)
  have a_u0 := Type100.u_c (s + 1)
  have a_u1 := Type100.u_a (s + 1)
  have a_u2 := Type100.u_b (s + 1)
  have a_r0 := Type100.rho_c (s + 1)
  have a_r1 := Type100.rho_a (s + 1)
  have a_r2 := Type100.rho_b (s + 1)
  have b_uv0 : (Type101.action s).φuv (𝔤 s 0) = (-3 : ℤ) • (𝔤 s 0) + (-2 : ℤ) • (𝔤 s 1) +
      (-2 : ℤ) • (𝔤 s 2) :=
    Type101.uv_c s
  have b_uv1 : (Type101.action s).φuv (𝔤 s 1) =
      (2 : ℤ) • (𝔤 s 0) + (1 : ℤ) • (𝔤 s 1) + (2 * (2 ^ s) + 2 : ℤ) • (𝔤 s 2) := Type101.uv_a s
  have b_uv2 : (Type101.action s).φuv (𝔤 s 2) =
      (2 : ℤ) • (𝔤 s 0) + (4 * (2 ^ s) ^ 2 + 6 * (2 ^ s) + 2 : ℤ) • (𝔤 s 1) + (1 : ℤ) • (𝔤 s 2) :=
    Type101.uv_b s
  have b_t0 : (Type101.action s).φt (𝔤 s 0) = (1 : ℤ) • (𝔤 s 0) + (2 : ℤ) • (𝔤 s 1) := Type101.t_c s
  have b_t1 : (Type101.action s).φt (𝔤 s 1) = (2 * (2 ^ s) - 1 : ℤ) • (𝔤 s 1) := Type101.t_a s
  have b_t2 : (Type101.action s).φt (𝔤 s 2) = (-4 * (2 ^ s) - 2 : ℤ) • (𝔤 s 0) +
      (-2 * (2 ^ s) - 2 : ℤ) • (𝔤 s 1) + (-2 * (2 ^ s) - 1 : ℤ) • (𝔤 s 2) := Type101.t_b s
  have b_u0 : (Type101.action s).φu (𝔤 s 0) = (1 : ℤ) • (𝔤 s 0) := Type101.u_c s
  have b_u1 : (Type101.action s).φu (𝔤 s 1) = (1 : ℤ) • (𝔤 s 2) := Type101.u_a s
  have b_u2 : (Type101.action s).φu (𝔤 s 2) = (1 : ℤ) • (𝔤 s 1) := Type101.u_b s
  have b_r0 : (Type101.action s).φρ (𝔤 s 0) = (1 : ℤ) • (𝔤 s 0) := Type101.rho_c s
  have b_r1 : (Type101.action s).φρ (𝔤 s 1) = (1 : ℤ) • (𝔤 s 2) := Type101.rho_a s
  have b_r2 : (Type101.action s).φρ (𝔤 s 2) = (-2 : ℤ) • (𝔤 s 0) + (-1 : ℤ) • (𝔤 s 1) +
      (-1 : ℤ) • (𝔤 s 2) :=
    Type101.rho_b s
  simp only [Torus.c, Torus.a, Torus.b] at a_uv0 a_uv1 a_uv2 a_t0 a_t1 a_t2
  simp only [Torus.c, Torus.a, Torus.b] at a_u0 a_u1 a_u2 a_r0 a_r1 a_r2
  obtain ⟨t, rfl | rfl⟩ := Int.even_or_odd' q
  ·
    have z1 : tor300 s 0 0 (2 * t) = 0 := by
      rw [← tor300_zero]; exact tor300_congr (by omega) (by omega) ⟨-t, by ring⟩
    have z2 : tor300 s 0 (2 * t) 0 = 0 := by
      rw [← tor300_zero]; exact tor300_congr (by omega) ⟨-t, by ring⟩ (by omega)
    have z3 : tor300 s (0 - 4 * (2 * t)) (-(2 * t)) (0 - 2 * t) = 0 := by
      rw [← tor300_zero]; exact tor300_congr ⟨4 * t, by ring⟩ ⟨t, by ring⟩ ⟨t, by ring⟩
    have z4 : tor300 s (0 - 4 * 0) (-0) (2 * t - 0) = 0 := by
      rw [← tor300_zero]; exact tor300_congr (by omega) (by omega) ⟨-t, by ring⟩
    rw [z1] at hV1e
    rw [z2] at hV2e
    rw [z3] at hW1 hW2
    rw [z4] at hW1
    left
    have h0 : V (𝔤 s 0) = (Type100.action (s + 1)).φuv (𝔤 s 0) ∧
        W (𝔤 s 0) = (Type100.action (s + 1)).φt (𝔤 s 0) ∧
        U (𝔤 s 0) = (Type100.action (s + 1)).φu (𝔤 s 0) ∧
            R (𝔤 s 0) = (Type100.action (s + 1)).φρ (𝔤 s 0) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hV0, a_uv0]
      · rw [hW0, a_t0]; module
      · rw [hU0, a_u0]; module
      · rw [hR0, a_r0]; module
    have h1 : V (𝔤 s 1) = (Type100.action (s + 1)).φuv (𝔤 s 1) ∧
        W (𝔤 s 1) = (Type100.action (s + 1)).φt (𝔤 s 1) ∧
        U (𝔤 s 1) = (Type100.action (s + 1)).φu (𝔤 s 1) ∧
            R (𝔤 s 1) = (Type100.action (s + 1)).φρ (𝔤 s 1) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hV1e, a_uv1]; module
      · rw [hW1, a_t1]; module
      · rw [hUe, a_u1]; module
      · rw [hR1, a_r1]; module
    have h2 : V (𝔤 s 2) = (Type100.action (s + 1)).φuv (𝔤 s 2) ∧
        W (𝔤 s 2) = (Type100.action (s + 1)).φt (𝔤 s 2) ∧
        U (𝔤 s 2) = (Type100.action (s + 1)).φu (𝔤 s 2) ∧
            R (𝔤 s 2) = (Type100.action (s + 1)).φρ (𝔤 s 2) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hV2e, a_uv2]; module
      · rw [hW2, a_t2]; module
      · rw [hU2e, a_u2]; module
      · rw [hR2, a_r2]
    intro j
    fin_cases j
    exacts [h0, h1, h2]
  ·
    right
    have h0 : V (𝔤 s 0) = (Type101.action s).φuv (𝔤 s 0) ∧
        W (𝔤 s 0) = (Type101.action s).φt (𝔤 s 0) ∧
        U (𝔤 s 0) = (Type101.action s).φu (𝔤 s 0) ∧ R (𝔤 s 0) = (Type101.action s).φρ (𝔤 s 0) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hV0, b_uv0]
      · rw [hW0, b_t0]; module
      · rw [hU0, b_u0]; module
      · rw [hR0, b_r0]; module
    have h1 : V (𝔤 s 1) = (Type101.action s).φuv (𝔤 s 1) ∧
        W (𝔤 s 1) = (Type101.action s).φt (𝔤 s 1) ∧
        U (𝔤 s 1) = (Type101.action s).φu (𝔤 s 1) ∧ R (𝔤 s 1) = (Type101.action s).φρ (𝔤 s 1) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hV1e, b_uv1]
        calc _ = (2 : ℤ) • (𝔤 s 0) + (1 : ℤ) • (𝔤 s 1) +
            (2 + (2 * t + 1) * 2 ^ (s + 1)) • (𝔤 s 2) := by
              simp only [tor300]; module
          _ = _ := by
              apply zsmul_gens_eq_of_dvd
              · simp
              · simp
              · change (2 : ℤ) ^ (s + 1 + 1) ∣ _
                exact ⟨-t, by ring⟩
      · rw [hW1, b_t1]
        calc _ = (4 * (2 * t + 1) * 2 ^ s) • (𝔤 s 0) + (-1 + (2 * t + 1) * 2 ^ (s + 1)) • (𝔤 s 1) +
              (0 : ℤ) • (𝔤 s 2) := by
              simp only [tor300]; module
          _ = (0 : ℤ) • (𝔤 s 0) + (2 * (2 ^ s) - 1 : ℤ) • (𝔤 s 1) + (0 : ℤ) • (𝔤 s 2) := by
              apply zsmul_gens_eq_of_dvd
              · change (2 : ℤ) ^ (s + 1) ∣ _
                exact ⟨-(4 * t + 2), by ring⟩
              · change (2 : ℤ) ^ (s + 1 + 1) ∣ _
                exact ⟨-t, by ring⟩
              · simp
          _ = _ := by module
      · rw [hUe, b_u1]; module
      · rw [hR1, b_r1]; module
    have h2 : V (𝔤 s 2) = (Type101.action s).φuv (𝔤 s 2) ∧
        W (𝔤 s 2) = (Type101.action s).φt (𝔤 s 2) ∧
        U (𝔤 s 2) = (Type101.action s).φu (𝔤 s 2) ∧ R (𝔤 s 2) = (Type101.action s).φρ (𝔤 s 2) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hV2e, b_uv2]
        calc _ = (2 : ℤ) • (𝔤 s 0) + (2 + (2 * t + 1) * 2 ^ (s + 1)) • (𝔤 s 1) +
            (1 : ℤ) • (𝔤 s 2) := by
              simp only [tor300]; module
          _ = _ := by
              apply zsmul_gens_eq_of_dvd
              · simp
              · change (2 : ℤ) ^ (s + 1 + 1) ∣ _
                exact ⟨2 ^ s + 1 - t, by ring⟩
              · simp
      · rw [hW2, b_t2]
        calc _ = (-2 - 4 * (2 * t + 1) * 2 ^ s) • (𝔤 s 0) +
            (-2 - (2 * t + 1) * 2 ^ (s + 1)) • (𝔤 s 1) +
              (-1 - (2 * t + 1) * 2 ^ (s + 1)) • (𝔤 s 2) := by
              simp only [tor300]; module
          _ = _ := by
              apply zsmul_gens_eq_of_dvd
              · change (2 : ℤ) ^ (s + 1) ∣ _
                exact ⟨4 * t, by ring⟩
              · change (2 : ℤ) ^ (s + 1 + 1) ∣ _
                exact ⟨t, by ring⟩
              · change (2 : ℤ) ^ (s + 1 + 1) ∣ _
                exact ⟨t, by ring⟩
      · rw [hU2e, b_u2]; module
      · rw [hR2, b_r2]
    intro j
    fin_cases j
    exacts [h0, h1, h2]

theorem R_tor300 {s : ℕ} (R : Torus (Type100.k (s + 1)) →+ Torus (Type100.k (s + 1)))
    (hR0 : R (𝔤 s 0) = (𝔤 s 0)) (hR1 : R (𝔤 s 1) = (𝔤 s 2))
    (hR2 : (2 : ℤ) • R (𝔤 s 2) = (-4 : ℤ) • (𝔤 s 0) + (-2 : ℤ) • (𝔤 s 1) +
        (-2 : ℤ) • (𝔤 s 2)) (x y z : ℤ) :
    R (tor300 s x y z) = tor300 s (x - 4 * z) (-z) (y - z) := by
  have e : tor300 s x y z =
      (x * 2 ^ s) • (𝔤 s 0) + (y * 2 ^ (s + 1)) • (𝔤 s 1) + (z * 2 ^ (s + 1)) • (𝔤 s 2) := rfl
  have e2 : (z * 2 ^ (s + 1)) • R (𝔤 s 2) = (z * 2 ^ s) • ((2 : ℤ) • R (𝔤 s 2)) := by
    rw [smul_smul, show z * 2 ^ s * 2 = z * 2 ^ (s + 1) by ring]
  rw [e, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hR0, hR1, e2, hR2]
  simp only [tor300]
  module

theorem U_tor300 {s : ℕ} (U : Torus (Type100.k (s + 1)) →+ Torus (Type100.k (s + 1)))
    (hU0 : U (𝔤 s 0) = (𝔤 s 0)) (hU1 : (2 : ℤ) • U (𝔤 s 1) = (2 : ℤ) • (𝔤 s 2))
    (hU2 : (2 : ℤ) • U (𝔤 s 2) = (2 : ℤ) • (𝔤 s 1)) (x y z : ℤ) :
    U (tor300 s x y z) = tor300 s x z y := by
  have e : tor300 s x y z =
      (x * 2 ^ s) • (𝔤 s 0) + (y * 2 ^ (s + 1)) • (𝔤 s 1) + (z * 2 ^ (s + 1)) • (𝔤 s 2) := rfl
  have e1 : (y * 2 ^ (s + 1)) • U (𝔤 s 1) = (y * 2 ^ s) • ((2 : ℤ) • U (𝔤 s 1)) := by
    rw [smul_smul, show y * 2 ^ s * 2 = y * 2 ^ (s + 1) by ring]
  have e2 : (z * 2 ^ (s + 1)) • U (𝔤 s 2) = (z * 2 ^ s) • ((2 : ℤ) • U (𝔤 s 2)) := by
    rw [smul_smul, show z * 2 ^ s * 2 = z * 2 ^ (s + 1) by ring]
  rw [e, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hU0, e1, e2, hU1, hU2]
  simp only [tor300]
  module

theorem rho_normalize300 {s : ℕ} (R : Torus (Type100.k (s + 1)) →+ Torus (Type100.k (s + 1)))
    (hRRR : ∀ w, R (R (R w)) = w) (hR0 : R (𝔤 s 0) = (𝔤 s 0)) (hR1 : R (𝔤 s 1) = (𝔤 s 2))
    (hR2 : (2 : ℤ) • R (𝔤 s 2) = (-4 : ℤ) • (𝔤 s 0) + (-2 : ℤ) • (𝔤 s 1) + (-2 : ℤ) • (𝔤 s 2)) :
    ∃ w : ℤ, ((𝔤 s 1) + tor300 s w 0 0) + R ((𝔤 s 1) + tor300 s w 0 0) +
      R (R ((𝔤 s 1) + tor300 s w 0 0)) = (-2 : ℤ) • (𝔤 s 0) := by
  obtain ⟨w0, w1, w2, hω⟩ := exists_tor300 (s := s)
    (w := R (𝔤 s 2) - ((-2 : ℤ) • (𝔤 s 0) + (-1 : ℤ) • (𝔤 s 1) + (-1 : ℤ) • (𝔤 s 2)))
        (by rw [smul_sub, hR2]; module)
  have hR2' : R (𝔤 s 2) = (-2 : ℤ) • (𝔤 s 0) + (-1 : ℤ) • (𝔤 s 1) + (-1 : ℤ) • (𝔤 s 2) +
      tor300 s w0 w1 w2 := by
    rw [← hω]; abel
  have hRt := R_tor300 R hR0 hR1 hR2
  have hRRf : R (R (𝔤 s 2)) = (𝔤 s 1) - tor300 s w0 w1 w2 +
      tor300 s (w0 - 4 * w2) (-w2) (w1 - w2) := by
    rw [hR2']
    simp only [map_add, map_zsmul, hR0, hR1, hR2', hRt]
    module
  have hω0 : 2 ∣ w1 ∧ 2 ∣ w2 := by
    have h := hRRR (𝔤 s 1)
    rw [hR1, hRRf] at h
    have key : tor300 s ((w0 - 4 * w2) - w0) ((-w2) - w1) ((w1 - w2) - w2) = tor300 s 0 0 0 := by
      simp only [tor300] at h ⊢
      linear_combination (norm := module) h
    rw [tor300_eq_iff] at key
    omega
  refine ⟨w0, ?_⟩
  simp only [map_add, hR1, hRRf, hRt]
  have e1 : tor300 s w0 w1 w2 = tor300 s w0 0 0 := tor300_congr (by omega) (by omega) (by omega)
  rw [hR2', e1]
  have hz : tor300 s (4 * w0) 0 0 = 0 := by
    rw [← tor300_zero]
    exact tor300_congr ⟨-2 * w0, by ring⟩ (by omega) (by omega)
  calc _ = (-2 : ℤ) • (𝔤 s 0) + tor300 s (4 * w0) 0 0 := by
        simp only [tor300]
        module
    _ = (-2 : ℤ) • (𝔤 s 0) := by rw [hz, add_zero]

end CFSG.CGT.Stroth77
