module

public import CFSG.ClassicalGroups.Orthogonal.Derived

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

namespace OmSeven

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem reflect_neg_vec (v : V) : reflect Q (-v) = reflect Q v := by
  by_cases hv : Q v = 0
  · rw [reflect_of_map_eq_zero hv,
      reflect_of_map_eq_zero (by rw [QuadraticMap.map_neg, hv])]
  · have hv' : Q (-v) ≠ 0 := by rwa [QuadraticMap.map_neg]
    refine LinearEquiv.ext fun x => ?_
    rw [reflect_apply hv, reflect_apply hv', polar_neg_left, QuadraticMap.map_neg, neg_div,
      neg_smul, smul_neg, neg_neg]

theorem reflect_mul_comm_of_polar_eq_zero {v w : V} (h : polar Q v w = 0) :
    reflect Q v * reflect Q w = reflect Q w * reflect Q v := by
  have h1 := reflect_conj (reflect_mem_orthogonalGroup Q v) w
  rw [reflect_apply_of_polar_eq_zero h] at h1
  exact mul_inv_eq_iff_eq_mul.1 h1

theorem reflect_apply_vec_self {v : V} (hv : Q v ≠ 0) : reflect Q v v = -v := by
  rw [reflect_apply hv, polar_self_eq_two_mul, mul_div_assoc, div_self hv, mul_one]
  module

theorem reflect_mul_reflect_pow_three {x y : V} (hxy : Q x = Q y) (hB : polar Q x y = Q y)
    (hy : Q y ≠ 0) : (reflect Q x * reflect Q y) ^ 3 = 1 := by
  have hx : Q x ≠ 0 := hxy ▸ hy
  have hay : reflect Q x y = y - x := by
    rw [reflect_apply hx, hB, ← hxy, div_self hx, one_smul]
  have hbx : reflect Q y x = x - y := by
    rw [reflect_apply hy, polar_comm, hB, div_self hy, one_smul]
  have h1 := reflect_conj (reflect_mem_orthogonalGroup Q x) y
  have h2 := reflect_conj (reflect_mem_orthogonalGroup Q y) x
  rw [reflect_inv, hay] at h1
  rw [reflect_inv, hbx] at h2
  have h3 : reflect Q (y - x) = reflect Q (x - y) := by
    rw [← neg_sub, reflect_neg_vec]
  calc (reflect Q x * reflect Q y) ^ 3
      = (reflect Q x * reflect Q y * reflect Q x) * (reflect Q y * reflect Q x * reflect Q y) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = reflect Q (y - x) * reflect Q (x - y) := by rw [h1, h2]
    _ = 1 := by rw [h3, reflect_mul_self]

end OmSeven

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
