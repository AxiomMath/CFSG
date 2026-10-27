module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.HardMathSupport.Malle.Proving

open Matrix CFSG.LocalAnalysis.ComponentInitial

theorem proj_pow_three_ne_one_four {K : Type*} [Field K]
    [CharP K 3] {A : Matrix.SpecialLinearGroup (Fin 4) K}
    (hA : A ∈ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.unitriangular 4 K)
    (h01 : (A : Matrix (Fin 4) (Fin 4) K) 0 1 ≠ 0) (h12 : (A : Matrix (Fin 4) (Fin 4) K) 1 2 ≠ 0)
    (h23 : (A : Matrix (Fin 4) (Fin 4) K) 2 3 ≠ 0) :
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 4 K A ^ 3 ≠ 1 := by
  intro h
  rw [← map_pow, LinearFlag.proj_eq_one_iff] at h
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.mp h
  have hz : ∀ i j : Fin 4, j < i → (A : Matrix (Fin 4) (Fin 4) K) i j = 0 := hA.1
  have hd : ∀ i : Fin 4, (A : Matrix (Fin 4) (Fin 4) K) i i = 1 := hA.2
  have hcube : ((A ^ 3 : Matrix.SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 3 = 0 := by
    rw [hc, scalar_apply, diagonal_apply_ne _ (show (0 : Fin 4) ≠ 3 by decide)]
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_three'] at hcube
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have key : ((A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) *
      (A : Matrix (Fin 4) (Fin 4) K)) 0 3 =
      (A : Matrix (Fin 4) (Fin 4) K) 0 1 * (A : Matrix (Fin 4) (Fin 4) K) 1 2 *
        (A : Matrix (Fin 4) (Fin 4) K) 2 3 + 3 *
        ((A : Matrix (Fin 4) (Fin 4) K) 0 3 + (A : Matrix (Fin 4) (Fin 4) K) 0 1 *
          (A : Matrix (Fin 4) (Fin 4) K) 1 3 + (A : Matrix (Fin 4) (Fin 4) K) 0 2 *
          (A : Matrix (Fin 4) (Fin 4) K) 2 3) := by
    simp only [Matrix.mul_apply, Fin.sum_univ_four,
      hz 1 0 (by decide), hz 2 0 (by decide), hz 3 0 (by decide),
      hz 2 1 (by decide), hz 3 1 (by decide), hz 3 2 (by decide),
      hd 0, hd 1, hd 2, hd 3]
    ring
  rw [key, h3, zero_mul, add_zero] at hcube
  exact mul_ne_zero (mul_ne_zero h01 h12) h23 hcube

end CFSG.HardMathSupport.Malle.Proving
