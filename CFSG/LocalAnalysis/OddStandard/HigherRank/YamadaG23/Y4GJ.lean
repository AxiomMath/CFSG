module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G]

theorem y4_comm_mem_omega1 {J : Subgroup G} (hJ : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a)
    (hexp : ∀ j ∈ J, j ^ 4 = 1) {x : G} (hx : x ∈ normalizer (J : Set G))
    (hxΩ : ∀ w ∈ omega1 J, x * w * x⁻¹ = w) : ∀ j ∈ J, ⁅x, j⁆ ∈ omega1 J := by
  intro j hj
  have hj' : x * j * x⁻¹ ∈ J := ((Subgroup.mem_normalizer_iff.mp hx) j).mp hj
  have hj2 : j ^ 2 ∈ omega1 J :=
    Subgroup.subset_closure ⟨J.pow_mem hj 2, by
      rw [← pow_mul, show (2 : ℕ) * 2 = 4 from rfl]
      exact hexp j hj⟩
  have hconj : (x * j * x⁻¹) ^ 2 = j ^ 2 := by
    rw [conj_pow, hxΩ (j ^ 2) hj2]
  have hc : ⁅x, j⁆ = (x * j * x⁻¹) * j⁻¹ := by
    rw [commutatorElement_def]
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [hc]; exact J.mul_mem hj' (J.inv_mem hj)
  · rw [hc]
    have hcomm : Commute (x * j * x⁻¹) j⁻¹ := hJ _ hj' _ (J.inv_mem hj)
    rw [hcomm.mul_pow 2, hconj, inv_pow, mul_inv_cancel]

end CFSG.OddStandard.HigherRank.YamadaG23
