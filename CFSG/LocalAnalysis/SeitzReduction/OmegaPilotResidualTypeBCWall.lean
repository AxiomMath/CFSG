module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBCLift

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module LinearMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem commute_of_wall_isometry [FiniteDimensional K V]
    (hB : (QuadraticMap.polarBilin Q).Nondegenerate) (N : V →ₗ[K] V)
    (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))
    {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hT : ∀ b, ∃ c, g (N b) = N c ∧
      ∀ a, QuadraticMap.polar Q (g (N a)) c = QuadraticMap.polar Q (N a) b) (x : V) :
    g (N x) = N (g x) := by
  have hle : (LinearMap.range N).map (g : V →ₗ[K] V) ≤ LinearMap.range N := by
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    obtain ⟨c, hc, -⟩ := hT b
    exact ⟨c, hc.symm⟩
  have heq : (LinearMap.range N).map (g : V →ₗ[K] V) = LinearMap.range N :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq g _)
  obtain ⟨c, hc, hca⟩ := hT x
  rw [hc]
  rw [← sub_eq_zero, ← map_sub]
  refine hB.2 _ fun a' => ?_
  rw [← hadj, QuadraticMap.polarBilin_apply_apply]
  have hmem : N a' ∈ (LinearMap.range N).map (g : V →ₗ[K] V) := by
    rw [heq]
    exact LinearMap.mem_range_self N a'
  obtain ⟨_, ⟨a, rfl⟩, ha⟩ := hmem
  change g (N a) = N a' at ha
  rw [← ha, QuadraticMap.polar_sub_right, hca, polar_apply_of_mem_orth hg, sub_self]

end CFSG.SeitzReduction.OmegaPilot
