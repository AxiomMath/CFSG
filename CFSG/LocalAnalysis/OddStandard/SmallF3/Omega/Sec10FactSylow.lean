module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelT0

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

theorem asc82FactSylow5_of_cert :
    Asc82FactSylow5 := by
  intro G _ _ L hL P hP
  obtain ⟨F0⟩ := exists_pspFrame hL
  obtain ⟨F, hF⟩ := F0.exists_frame_syl hP
  have hPL : P ≤ L := hP.1
  refine ⟨?_, fun g hg hc => ?_⟩
  · rw [← F.card_centerIn_img hPL, hF]
    exact card_centerIn_QT0
  · let y : ↥(normalizer (L : Set G)) := ⟨g, hg⟩
    have hy : ∀ t ∈ QT0.originalSubgroup, F.φ y * t = t * F.φ y := by
      intro t ht
      rw [← hF] at ht
      obtain ⟨l, hl, rfl⟩ := PspFrame.mem_img.1 ht
      exact (F.comm_phi_psi_iff y l).2 (hc l hl)
    have hcen := centralizer_QT0_le (F.mem_A y) hy
    rw [← hF, ← F.img_centerIn hPL] at hcen
    obtain ⟨l, hl, hlφ⟩ := PspFrame.mem_img.1 hcen
    exact F.mem_sup_of_phi_eq_psi y l hl hlφ.symm

end CFSG.OddStandard.SmallF3.Omega
