module

public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXCentralLift

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix Matrix.ProjGenLinGroup CFSG.Open LinearFlag CFSG.LocalAnalysis.GorensteinLyons
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation toGL_slConjugation)

variable {F : Type} [Field F] [Finite F]

theorem mem_semilinearAutGroup_of_pow {n p : ℕ} (hn : 3 ≤ n) (hp : Odd p)
    {x : MulAut (projectiveSL n F)} (hx : x ^ p = 1) : x ∈ semilinearAutGroup n F := by
  have := finite_mulAut_projectiveSL (F := F) n
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (K := F) (n := n)
  rw [(automorphism_generation (K := F) hn).1] at hidx
  have hidx' : (semilinearAutGroup n F).index ≤ 2 := by
    rw [← Subgroup.relIndex_top_right]
    exact hidx
  have hne : (semilinearAutGroup n F).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (show (semilinearAutGroup n F).index = 1 ∨ (semilinearAutGroup n F).index = 2 by
    omega) with h1 | h2
  · rw [Subgroup.index_eq_one.1 h1]
    exact Subgroup.mem_top x
  · have hsq := Subgroup.sq_mem_of_index_two h2 x
    obtain ⟨k, rfl⟩ := hp
    have hxk : x = ((x ^ 2) ^ k)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_mul, ← pow_succ']
      exact hx
    rw [hxk]
    exact inv_mem (pow_mem hsq k)

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
