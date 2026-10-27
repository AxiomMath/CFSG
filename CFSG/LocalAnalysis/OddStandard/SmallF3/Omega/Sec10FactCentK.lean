module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactPockets
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelCentK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PocketsSup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

theorem asc82FactCentK5_of_cert :
    Asc82FactCentK5 := by
  intro G _ _ L hL z hz2 K1 K2 hK1 hK2 hne y hyN hcomm
  obtain ⟨F, hzL, hF⟩ := Pk.exists_frame_tA hL ⟨hz2, K1, hK1⟩
  have hsup := pockets_sup_eq asc82FactPockets5_of_cert hL hz2 hK1 hK2 hne
  have hCL : L ⊓ centralizer ({z} : Set G) ≤ L := inf_le_left
  have hC : F.img (L ⊓ centralizer ({z} : Set G)) =
      QP45.originalSubgroup ⊓ centralizer ({Certificates.P43Twin.tA ()} : Set P45) := by
    have h := F.img_inf_centralizer_singleton ⟨z, hzL⟩
    rw [hF] at h
    exact h
  let y' : ↥(normalizer (L : Set G)) := ⟨y, hyN⟩
  have hφy : F.φ y' = 1 ∨ F.φ y' = Certificates.P43Twin.tA () := by
    refine eq_of_comm_oddL (F.mem_A y') fun x hx hodd => ?_
    have hxO : x ∈ F.img (K1 ⊔ K2) := by
      rw [hsup.1, F.img_oTwoRes hCL, hC]
      exact Subgroup.subset_closure ⟨hx, hodd⟩
    obtain ⟨l, hl, rfl⟩ := PspFrame.mem_img.1 hxO
    exact (F.comm_phi_psi_iff y' l).2 (hcomm (l : G) hl)
  rcases hφy with h | h
  · exact Subgroup.mem_sup_left ((F.ker_iff y').1 h)
  · have hh : F.φ y' = F.ψ ⟨z, hzL⟩ := by rw [hF]; exact h
    exact F.mem_sup_of_phi_eq_psi y' ⟨z, hzL⟩ (Subgroup.mem_zpowers z) hh

end CFSG.OddStandard.SmallF3.Omega
