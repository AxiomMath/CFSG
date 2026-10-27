module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelF1051
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PocketsSup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameSylow
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

local notation "z0" => Certificates.OmegaT0.z0 ()

theorem exists_frame_Q32
    (hP5 : Asc82FactPockets5) {G : Type} [Group G] [Finite G] {L P : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hL : IsPSp43 L) (hP : IsSylow2Of P L) (hzP : z ∈ centerIn P)
    (hz2 : orderOf z = 2) (hK1 : Sl23PocketIn L z K1) (hK2 : Sl23PocketIn L z K2) (hne : K1 ≠ K2) :
    ∃ F : PspFrame L, F.img P = QT0.originalSubgroup ∧ secQ K1 K2 ≤ L ∧
      F.img (secQ K1 K2) = Q32 := by
  obtain ⟨F0⟩ := exists_pspFrame hL
  obtain ⟨F, hFP⟩ := F0.exists_frame_syl hP
  have hPL : P ≤ L := hP.1
  have hzL : z ∈ L := hPL (centerIn_le P hzP)
  obtain ⟨zL, rfl⟩ : ∃ zL : ↥L, (zL : G) = z := ⟨⟨z, hzL⟩, rfl⟩
  have hψz : F.ψ zL = z0 := by
    have h1 : F.ψ zL ∈ F.img (centerIn P) := PspFrame.psi_mem_img.2 hzP
    rw [F.img_centerIn hPL, hFP] at h1
    rcases eq_z0_of_mem_centerIn h1 with h | h
    · exfalso
      have h3 := F.orderOf_psi zL
      rw [h, orderOf_one] at h3
      have h4 : orderOf (zL : G) = 2 := hz2
      omega
    · exact h
  have hsup := pockets_sup_eq hP5 hL hz2 hK1 hK2 hne
  have hCL : L ⊓ centralizer ({(zL : G)} : Set G) ≤ L := inf_le_left
  have hXC : K1 ⊔ K2 ≤ L ⊓ centralizer ({(zL : G)} : Set G) := hsup.1 ▸ PspFrame.oTwoRes_le _
  have hXL : K1 ⊔ K2 ≤ L := hXC.trans inf_le_left
  have himgC : F.img (L ⊓ centralizer ({(zL : G)} : Set G)) =
      QP45.originalSubgroup ⊓ centralizer ({z0} : Set P45) := by
    rw [F.img_inf_centralizer_singleton zL, hψz]
  have hcardC : Nat.card ↥(L ⊓ centralizer ({(zL : G)} : Set G)) = 576 := by
    rw [← F.card_img hCL, himgC, card_inf_centralizer QP45 QP45_ok z0]
    exact length_CL0
  have hcardX : Nat.card ↥(K1 ⊔ K2) = 288 := by
    have h := Subgroup.relIndex_mul_card (H := K1 ⊔ K2)
      (K := L ⊓ centralizer ({(zL : G)} : Set G))
    rw [inf_eq_left.2 hXC, hsup.2, hcardC] at h
    omega
  have himgX : F.img (K1 ⊔ K2) = oTwoC := by
    rw [hsup.1, F.img_oTwoRes hCL, himgC]
    rfl
  have h288 : Nat.card ↥oTwoC = 288 := by
    rw [← himgX, F.card_img hXL, hcardX]
  have hQ : F.img (secQ K1 K2) = Q32 := by
    show F.img (twoCoreIn (K1 ⊔ K2)) = Q32
    rw [F.img_twoCoreIn hXL, himgX, twoCoreIn_oTwoC h288]
  exact ⟨F, hFP, (twoCoreIn_le_self (K1 ⊔ K2)).trans hXL, hQ⟩

end CFSG.OddStandard.SmallF3.Omega
