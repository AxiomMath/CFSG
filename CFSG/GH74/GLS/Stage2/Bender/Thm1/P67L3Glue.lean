module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Odd
variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem mem_semilinearAutGroup_of_pow_eq_one {m : ℕ} (hn : 3 ≤ n) (hm : Odd m)
    {v : MulAut (projectiveSL n K)} (hv : v ^ m = 1) : v ∈ semilinearAutGroup n K := by
  have hR : v ∈ standardAutGroup n K := by rw [(automorphism_generation hn).1]; trivial
  rcases mem_or_mul_dualAut_mem hR with h | h
  · exact h
  · have hδδ : dualAut n K * dualAut n K = 1 :=
      (standard_automorphism_transport (K := K) (n := n)).2.2.2.1
    have hv2 : v ^ 2 ∈ semilinearAutGroup n K := by
      have h1 := dualAut_mul_mul_dualAut_mem h
      have : v ^ 2 = (v * dualAut n K) * (dualAut n K * (v * dualAut n K) * dualAut n K) := by
        calc v ^ 2 = v * (dualAut n K * dualAut n K) * v * (dualAut n K * dualAut n K) := by
              rw [hδδ, mul_one, mul_one, pow_two]
          _ = _ := by group
      rw [this]
      exact mul_mem h h1
    obtain ⟨k, hk⟩ := hm
    have hvv : v = (v ^ 2) ^ (k + 1) := by
      calc v = v ^ m * v := by rw [hv, one_mul]
        _ = (v ^ 2) ^ (k + 1) := by rw [← pow_succ, ← pow_mul, hk]; congr 1
    rw [hvv]
    exact Subgroup.pow_mem _ hv2 _

end Odd

section Conj
variable {Y : Type} [Group Y]

theorem congr_eq_mul_mul_inv (φ α : MulAut Y) : MulAut.congr φ α = φ * α * φ⁻¹ := by
  ext y
  simp [MulAut.congr_apply]

end Conj

end CFSG.GH74.GLS.Stage2.Bender.Thm1
