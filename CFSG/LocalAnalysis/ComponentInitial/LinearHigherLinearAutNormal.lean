module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration

public section

namespace CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type*} [Field K] {n : ℕ}

theorem linearAutGroup_normal_of_three_le [Finite K] (hn : 3 ≤ n) :
    (linearAutGroup n K).Normal := by
  obtain ⟨-, -, hD, -⟩ := standard_outer_quotients (n := n) (K := K)
  obtain ⟨hR, -⟩ := automorphism_generation (K := K) hn
  rw [hR] at hD
  exact ⟨fun d hd g => hD.conj_mem ⟨d, Subgroup.mem_top d⟩ hd ⟨g, Subgroup.mem_top g⟩⟩

theorem mem_semilinearAutGroup_of_pow_odd [Finite K] (hn : 3 ≤ n) {α : MulAut (projectiveSL n K)}
    {m : ℕ} (hm : Odd m) (hα : α ^ m = 1) : α ∈ semilinearAutGroup n K := by
  obtain ⟨hR, -⟩ := automorphism_generation (K := K) hn
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := n) (K := K)
  have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
    have h2 : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
    rwa [hR, Subgroup.relIndex_top_right] at h2
  have hsq : α ^ 2 ∈ semilinearAutGroup n K := by
    have hpos : 0 < (semilinearAutGroup n K).index := by
      have : Finite (MulAut (projectiveSL n K)) :=
        Finite.of_injective (fun β : MulAut (projectiveSL n K) => (β : projectiveSL n K → _))
          fun _ _ h => MulEquiv.ext (congrFun h)
      exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    interval_cases h : (semilinearAutGroup n K).index
    · rw [Subgroup.index_eq_one] at h
      rw [h]
      exact Subgroup.mem_top _
    · exact Subgroup.sq_mem_of_index_two h α
  obtain ⟨k, rfl⟩ := hm
  have hα' : α = (α ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ, hα, one_mul]
  rw [hα']
  exact Subgroup.pow_mem _ hsq _

end CFSG.LocalAnalysis.ComponentInitial.LinearFlag
