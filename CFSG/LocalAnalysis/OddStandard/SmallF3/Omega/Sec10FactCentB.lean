module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameB0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

theorem asc82FactCentB5_of_cert :
    Asc82FactCentB5 := by
  intro G _ _ L hL P hP g hg hcent
  obtain ⟨F0⟩ := exists_pspFrame hL
  obtain ⟨F, hFP⟩ := F0.exists_frame_syl hP
  have hJ := F.jElem_eq hFP hP.1
  rw [hJ] at hcent ⊢
  have hπ : F.φ ⟨g, hg⟩ ∈ B0 := by
    refine centralizer_B0_le (F.mem_A _) fun b hb => ?_
    obtain ⟨l, rfl⟩ := F.ψ_surj (B0_le_P hb)
    exact (F.comm_phi_psi_iff ⟨g, hg⟩ l).2 (hcent (l : G) (PspFrame.mem_pre.2 ⟨l.2, hb⟩))
  obtain ⟨l, hl⟩ := F.ψ_surj (B0_le_P hπ)
  have hlB : (l : G) ∈ F.pre B0 := PspFrame.mem_pre.2 ⟨l.2, hl ▸ hπ⟩
  rw [sup_comm]
  exact F.mem_sup_of_phi_eq_psi ⟨g, hg⟩ l hlB hl.symm

end CFSG.OddStandard.SmallF3.Omega
