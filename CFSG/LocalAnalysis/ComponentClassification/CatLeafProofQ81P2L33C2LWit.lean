module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2Rows

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem pow_three_of_rel {R : Type*} [Ring R] (hadd : ∀ x : R, x + x = 0) {a b : R}
    (ha : a * a = 0) (hb : b * b = 0) (haba : a * b * a = a) (hbab : b * a * b = b) :
    ((1 + a) * (1 + b)) ^ 3 = 1 := by
  have hx : (1 + a) * (1 + a) = 1 := by
    rw [show (1 + a) * (1 + a) = 1 + (a + a) + a * a by noncomm_ring, ha, hadd, add_zero,
      add_zero]
  have hy : (1 + b) * (1 + b) = 1 := by
    rw [show (1 + b) * (1 + b) = 1 + (b + b) + b * b by noncomm_ring, hb, hadd, add_zero,
      add_zero]
  have hbr : (1 + a) * (1 + b) * (1 + a) = (1 + b) * (1 + a) * (1 + b) := by
    rw [show (1 + a) * (1 + b) * (1 + a) = 1 + b + a * b + b * a + (a + a) + a * a + a * b * a by
        noncomm_ring,
      show (1 + b) * (1 + a) * (1 + b) = 1 + a + b * a + a * b + (b + b) + b * b + b * a * b by
        noncomm_ring, ha, hb, haba, hbab, hadd, hadd]
    abel
  set x := 1 + a
  set y := 1 + b
  calc (x * y) ^ 3 = x * (y * x * y) * (x * y) := by rw [pow_three]; simp only [mul_assoc]
    _ = x * (x * y * x) * (x * y) := by rw [← hbr]
    _ = (x * x) * y * (x * x) * y := by simp only [mul_assoc]
    _ = 1 := by rw [hx, one_mul, mul_one, hy]

variable {n : ℕ} {K : Type} [Field K]

theorem add_self_eq_zero_of_two (h2 : (2 : K) = 0) (A : Matrix (Fin n) (Fin n) K) :
    A + A = 0 := by
  ext i j
  rw [Matrix.add_apply, ← two_mul, h2, zero_mul, Matrix.zero_apply]

theorem one_add_mul_self (h2 : (2 : K) = 0) {E : Matrix (Fin n) (Fin n) K} (hE : E * E = 0) :
    (1 + E) * (1 + E) = 1 := by
  rw [show (1 + E) * (1 + E) = 1 + (E + E) + E * E by noncomm_ring, hE,
    add_self_eq_zero_of_two h2, add_zero, add_zero]

theorem det_eq_one_of_mul_self (h2 : (2 : K) = 0) {M : Matrix (Fin n) (Fin n) K}
    (hM : M * M = 1) : M.det = 1 := by
  have hd : M.det * M.det = 1 := by rw [← det_mul, hM, det_one]
  have h0 : (M.det - 1) * (M.det - 1) = 0 := by
    rw [show (M.det - 1) * (M.det - 1) = M.det * M.det - 2 * M.det + 1 by ring, hd, h2,
      zero_mul, sub_zero, one_add_one_eq_two, h2]
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h0)

@[expose] def unipOf (h2 : (2 : K) = 0) (E : Matrix (Fin n) (Fin n) K) (hE : E * E = 0) :
    SpecialLinearGroup (Fin n) K :=
  ⟨1 + E, det_eq_one_of_mul_self h2 (one_add_mul_self h2 hE)⟩

@[simp]
theorem coe_unipOf (h2 : (2 : K) = 0) (E : Matrix (Fin n) (Fin n) K) (hE : E * E = 0) :
    (unipOf h2 E hE : Matrix (Fin n) (Fin n) K) = 1 + E :=
  rfl

theorem orderOf_proj_eq_two (h2 : (2 : K) = 0) {c : SpecialLinearGroup (Fin n) K}
    (hc2 : c * c = 1) (hc1 : c ≠ 1) : orderOf (proj n K c) = 2 := by
  apply orderOf_eq_prime
  · rw [sq, ← map_mul, hc2, map_one]
  · intro h1
    have hmem : c ∈ scalars n K := by
      rw [← ker_proj]
      exact h1
    obtain ⟨r, -, hr⟩ := mem_scalars.mp hmem
    apply hc1
    have hcc : ((c * c : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [hc2]
      rfl
    rw [Matrix.SpecialLinearGroup.coe_mul, hr, ← map_mul] at hcc
    ext i j
    have hii := congrFun (congrFun hcc i) i
    rw [scalar_apply, diagonal_apply_eq, one_apply_eq] at hii
    have hr1 : (r : K) = 1 := by
      have h0 : ((r : K) - 1) * ((r : K) - 1) = 0 := by
        rw [show ((r : K) - 1) * ((r : K) - 1) = r * r - 2 * r + 1 by ring, hii, h2, zero_mul,
          sub_zero, one_add_one_eq_two, h2]
      exact sub_eq_zero.mp (mul_self_eq_zero.mp h0)
    rw [hr, hr1, map_one]
    rfl

theorem hasWit_of_sl (h2 : (2 : K) = 0) {v : MulAut (projectiveSL n K)}
    (h : SpecialLinearGroup (Fin n) K) {m : ℕ} (hm : Odd m) (hhm : h ^ m = 1)
    {E : Matrix (Fin n) (Fin n) K} (hE : E * E = 0)
    (hEh : E * (h : Matrix (Fin n) (Fin n) K) * E = 0)
    (hEh' : E * ((h⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * E = 0)
    (hne : (h : Matrix (Fin n) (Fin n) K) * E ≠ E * h)
    (hvh : v (proj n K h) = proj n K h)
    (hvu : v (proj n K (unipOf h2 E hE)) = proj n K (unipOf h2 E hE)) : HasWit v := by
  obtain ⟨u, hu⟩ : ∃ u, u = unipOf h2 E hE := ⟨_, rfl⟩
  rw [← hu] at hvu
  obtain ⟨H, hH⟩ : ∃ H, H = (h : Matrix (Fin n) (Fin n) K) := ⟨_, rfl⟩
  obtain ⟨H', hH'⟩ : ∃ H', H' = ((h⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    ⟨_, rfl⟩
  rw [← hH] at hEh hne
  rw [← hH'] at hEh'
  have hHH' : H * H' = 1 := by
    rw [hH, hH', ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hH'H : H' * H = 1 := by
    rw [hH, hH', ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have huu : u * u = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, hu, coe_unipOf, one_add_mul_self h2 hE]
    rfl
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  obtain ⟨c, hc⟩ : ∃ c, c = h * u * h⁻¹ * u⁻¹ := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = H * E * H' + E := ⟨_, rfl⟩
  have hcM : (c : Matrix (Fin n) (Fin n) K) = 1 + M := by
    rw [hc, hui, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hu, coe_unipOf, ← hH, ← hH']
    rw [show H * (1 + E) * H' * (1 + E) = H * H' + H * E * H' + E * 1 + H * (E * H' * E) - E +
        (H * H') * E by noncomm_ring, hHH', hEh', mul_zero, add_zero, mul_one, one_mul, hM]
    abel
  have hMM : M * M = 0 := by
    rw [hM, show (H * E * H' + E) * (H * E * H' + E) = H * (E * (H' * H) * E) * H' +
        H * (E * H' * E) + (E * H * E) * H' + E * E by noncomm_ring]
    simp only [hH'H, mul_one, hE, hEh, hEh', mul_zero, zero_mul, add_zero]
  have hc2 : c * c = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, hcM, one_add_mul_self h2 hMM]
    rfl
  have hc1 : c ≠ 1 := by
    intro h1
    apply hne
    have hM0 : M = 0 := by
      have := congrArg (fun g : SpecialLinearGroup (Fin n) K => (g : Matrix (Fin n) (Fin n) K))
        h1
      simp only [hcM, Matrix.SpecialLinearGroup.coe_one] at this
      simpa using this
    have hconj : H * E * H' = E := by
      have h0 : H * E * H' + E = 0 := hM ▸ hM0
      calc H * E * H' = H * E * H' + (E + E) := by rw [add_self_eq_zero_of_two h2, add_zero]
        _ = (H * E * H' + E) + E := by abel
        _ = E := by rw [h0, zero_add]
    calc H * E = H * E * (H' * H) := by rw [hH'H, mul_one]
      _ = (H * E * H') * H := by simp only [mul_assoc]
      _ = E * H := by rw [hconj]
  have hord : orderOf (proj n K c) = 2 := orderOf_proj_eq_two h2 hc2 hc1
  refine ⟨proj n K h, proj n K u, hvh, hvu, ?_, ?_⟩
  · exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hhm, map_one]))
  · have e : proj n K h * proj n K u * (proj n K h)⁻¹ * (proj n K u)⁻¹ = proj n K c := by
      rw [hc]
      simp only [map_mul, map_inv]
    rw [e, hord]

end CFSG.ComponentClassification.HarrisLit.L33.C2
