module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkFrame

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

theorem asc82FactPockets5_of_cert :
    Asc82FactPockets5 := by
  intro G _ _ L hL z hz
  obtain ⟨F, hzL, hF⟩ := Pk.exists_frame_tA hL hz
  have hXL : L ⊓ centralizer ({z} : Set G) ≤ L := inf_le_left
  have hC : F.img (L ⊓ centralizer ({z} : Set G)) = Pk.Cs := by
    have h := F.img_inf_centralizer_singleton ⟨z, hzL⟩
    rw [hF] at h
    exact h
  have hpocket : ∀ K : Subgroup G, K ≤ L →
      (Sl23PocketIn L z K ↔ Sl23PocketIn QP45.originalSubgroup Pk.tA (F.img K)) := by
    intro K hK
    have h := F.sl23PocketIn_img_iff hzL hK
    rwa [hF] at h
  have hKAP : Pk.KA ≤ QP45.originalSubgroup := Pk.KA_le.trans inf_le_left
  have hKBP : Pk.KB ≤ QP45.originalSubgroup := Pk.KB_le.trans inf_le_left
  have h1 : F.img (F.pre Pk.KA) = Pk.KA := PspFrame.img_pre hKAP
  have h2 : F.img (F.pre Pk.KB) = Pk.KB := PspFrame.img_pre hKBP
  have hK1L : F.pre Pk.KA ≤ L := PspFrame.pre_le _
  have hK2L : F.pre Pk.KB ≤ L := PspFrame.pre_le _
  have hP1 : Sl23PocketIn L z (F.pre Pk.KA) :=
    (hpocket _ hK1L).2 (by rw [h1]; exact Pk.sl23Pocket_KA)
  have hP2 : Sl23PocketIn L z (F.pre Pk.KB) :=
    (hpocket _ hK2L).2 (by rw [h2]; exact Pk.sl23Pocket_KB)
  have hsup : F.img (F.pre Pk.KA ⊔ F.pre Pk.KB) = Pk.KA ⊔ Pk.KB := by
    rw [F.img_sup hK1L hK2L, h1, h2]
  refine ⟨F.pre Pk.KA, F.pre Pk.KB, hP1, hP2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    apply Pk.KA_ne_KB
    rw [← h1, ← h2, h]
  · intro K hK
    have hKL := PspFrame.le_of_sl23PocketIn hK
    rcases Pk.pocket_tA_cases ((hpocket K hKL).1 hK) with h | h
    · left
      rw [← PspFrame.pre_img (F := F) hKL, h]
    · right
      rw [← PspFrame.pre_img (F := F) hKL, h]
  · have h := F.img_commutator hK1L hK2L
    rw [h1, h2, Pk.commutator_KAB, ← F.img_bot] at h
    exact (PspFrame.img_inj (Pk.commutator_le_of_le hK1L hK2L) bot_le).1 h
  · have h : F.img (oTwoRes (L ⊓ centralizer ({z} : Set G))) =
        F.img (F.pre Pk.KA ⊔ F.pre Pk.KB) := by
      rw [F.img_oTwoRes hXL, hC, Pk.oTwoRes_Cs, hsup]
    exact (PspFrame.img_inj ((PspFrame.oTwoRes_le _).trans hXL) (sup_le hK1L hK2L)).1 h
  · have h := PspFrame.relIndex_img (F := F) (sup_le hP1.2.1 hP2.2.1) hXL
    rw [hsup, hC] at h
    rw [← h]
    exact Pk.relIndex_E
  · intro g hg hgn
    have hgL : g ∈ L := (Subgroup.mem_inf.1 hg).1
    have hmem : F.ψ ⟨g, hgL⟩ ∈ Pk.Cs := by
      rw [← hC]
      exact PspFrame.psi_mem_img.2 hg
    have hnot : F.ψ ⟨g, hgL⟩ ∉ Pk.KA ⊔ Pk.KB := by
      rw [← hsup]
      exact fun h => hgn (PspFrame.psi_mem_img.1 h)
    have h4 := F.img_conjugate_psi (X := F.pre Pk.KA) ⟨g, hgL⟩
    rw [h1, Pk.conjugate_KA_eq hmem hnot, ← h2] at h4
    exact (PspFrame.img_inj (Pk.conjugate_le_of_le hK1L hgL) hK2L).1 h4

end CFSG.OddStandard.SmallF3.Omega
