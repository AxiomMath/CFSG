module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK4CoverAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IVAux6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec8t84t_gi_witness (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {ρ : ↥(simGroup Q)} (hρ : IsSimilitude Q (ρ : V ≃ₗ[ZMod 3] V) (-1))
    (hρρ : ∀ v, (ρ : V ≃ₗ[ZMod 3] V) ((ρ : V ≃ₗ[ZMod 3] V) v) = -v) :
    ∃ c ∈ fixSub (simAct Q ρ), c ∉ omegaGroup hQ := by
  obtain ⟨u₁, -, hu₁, -, -, h1R1, -, -, -⟩ := ff6m_K4_pair_facts hQ hdim hρ hρρ
  simp only [QuadraticMap.polarBilin_apply_apply] at h1R1
  have hQ₁ : Q u₁ ≠ 0 := by rw [hu₁]; decide
  have hQR₁ : Q ((ρ : V ≃ₗ[ZMod 3] V) u₁) = -1 := by rw [ff_k4iv_map_sim hρ, hu₁]
  have hQR₁' : Q ((ρ : V ≃ₗ[ZMod 3] V) u₁) ≠ 0 := by rw [hQR₁]; decide
  have hd1_fix := ff_k4iv_krefl_fixed hρ hρρ hQ₁ h1R1
  have hgg : (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)) *
      (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)) = 1 := by
    calc _ = (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)) *
          (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁))⁻¹ := by
          rw [ff_k4iv_dinv hρ hQ₁ h1R1]
      _ = 1 := mul_inv_cancel _
  have htype : invType (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)) = (2, 1) := by
    rw [reflTot_of_ne hQ₁, reflTot_of_ne hQR₁']
    exact ff_invType_reflPair hQ hQ₁ hQR₁' h1R1 hu₁ hQR₁
  refine ⟨_, mem_fixSub_iff.mpr hd1_fix, fun hΩ => ?_⟩
  have h2 := ((involution_mem_omegaGroup_iff hQ hgg).mp hΩ).2
  rw [show invSign (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)) = 1 from
      congrArg Prod.snd htype,
    show invDim (reflTot Q u₁ * reflTot Q ((ρ : V ≃ₗ[ZMod 3] V) u₁)) = 2 from
      congrArg Prod.fst htype] at h2
  revert h2
  decide

end CFSG.OddStandard.SmallF3.Omega
