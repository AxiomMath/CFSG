module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64iiNPC

open scoped Pointwise

theorem exists_mem_normalizer_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (S : Sylow p G) (D : Subgroup G) (hSD : (S : Subgroup G) ≤ D) (y : G)
    (hyD : ∀ s ∈ (S : Subgroup G), y * s * y⁻¹ ∈ D) :
    ∃ d ∈ D, d * y ∈ Subgroup.normalizer (S : Subgroup G) := by
  have hS₁D : ((y • S : Sylow p G) : Subgroup G) ≤ D := by
    intro z hz
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    simpa [MulAut.smul_def, MulAut.conj_apply] using hyD s hs
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D ((y • S : Sylow p G).subtype hS₁D)
    (S.subtype hSD)
  rw [Sylow.smul_subtype hS₁D d] at hd
  have h1 : (d : G) • (y • S : Sylow p G) = S := Sylow.subtype_injective hd
  refine ⟨d, d.2, ?_⟩
  exact (Sylow.smul_eq_iff_mem_normalizer (P := S) (g := (d : G) * y)).1
    (by rw [mul_smul]; exact h1)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKF64iiNPC
