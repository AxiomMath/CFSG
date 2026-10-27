module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Q2mModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactPockets
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PocketsSup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TypeDict2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109BInputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

local notation "z0" => Certificates.OmegaT0.z0 ()

theorem asc82FactQ2m_of_cert :
    Asc82FactQ2m := by
  intro G _ _ L hL z K1 K2 hz hK1 hK2 hne q hq hq2 hqz
  obtain ⟨F0, hzL, hF0⟩ := Pk.exists_frame_tA hL hz
  obtain ⟨c, hc, hcz⟩ := exists_conj_tA_z0
  let F : PspFrame L := F0.conj c hc
  have hψz : F.ψ ⟨z, hzL⟩ = z0 := by
    show c * F0.ψ ⟨z, hzL⟩ * c⁻¹ = z0
    rw [hF0]
    exact hcz
  have hsup := pockets_sup_eq asc82FactPockets5_of_cert hL hz.1 hK1 hK2 hne
  have hCL : L ⊓ centralizer ({z} : Set G) ≤ L := inf_le_left
  have hXC : K1 ⊔ K2 ≤ L ⊓ centralizer ({z} : Set G) := hsup.1 ▸ PspFrame.oTwoRes_le _
  have hXL : K1 ⊔ K2 ≤ L := hXC.trans inf_le_left
  have himgC : F.img (L ⊓ centralizer ({z} : Set G)) =
      QP45.originalSubgroup ⊓ centralizer ({z0} : Set P45) := by
    have h := F.img_inf_centralizer_singleton ⟨z, hzL⟩
    rw [hψz] at h
    exact h
  have hcardC : Nat.card ↥(L ⊓ centralizer ({z} : Set G)) = 576 := by
    rw [← F.card_img hCL, himgC, card_inf_centralizer QP45 QP45_ok z0]
    exact length_CL0
  have hcardX : Nat.card ↥(K1 ⊔ K2) = 288 := by
    have h := Subgroup.relIndex_mul_card (H := K1 ⊔ K2) (K := L ⊓ centralizer ({z} : Set G))
    rw [inf_eq_left.2 hXC, hsup.2, hcardC] at h
    omega
  have himgX : F.img (K1 ⊔ K2) = oTwoC := by
    rw [hsup.1, F.img_oTwoRes hCL, himgC]
    rfl
  have h288 : Nat.card ↥oTwoC = 288 := by
    rw [← himgX, F.card_img hXL, hcardX]
  have hQ : F.img (twoCoreIn (K1 ⊔ K2)) = Q32 := by
    rw [F.img_twoCoreIn hXL, himgX, twoCoreIn_oTwoC h288]
  have hqL : q ∈ L := hXL (twoCoreIn_le_self (K1 ⊔ K2) hq)
  have hqmem : F.ψ ⟨q, hqL⟩ ∈ Q32 := by
    rw [← hQ]
    exact F.psi_mem_img.2 hq
  have hq1 : q ≠ 1 := fun h => hqz (h ▸ one_mem _)
  have hqne : q ≠ z := fun h => hqz (h ▸ Subgroup.mem_zpowers z)
  have hψ1 : F.ψ ⟨q, hqL⟩ ≠ 1 := by
    intro h
    apply hq1
    exact congrArg Subtype.val (F.ψ_injective (h.trans (map_one F.ψ).symm))
  have hψz' : F.ψ ⟨q, hqL⟩ ≠ z0 := by
    intro h
    apply hqne
    exact congrArg Subtype.val (F.ψ_injective (h.trans hψz.symm))
  have hψsq : F.ψ ⟨q, hqL⟩ * F.ψ ⟨q, hqL⟩ = 1 := by
    rw [← map_mul, show (⟨q, hqL⟩ : ↥L) * ⟨q, hqL⟩ = 1 from Subtype.ext hq2, map_one]
  have hcnt : centCount (F.ψ ⟨q, hqL⟩) = 192 := centCount_of_mem_Q32 hqmem hψsq hψ1 hψz'
  have hqN : q ∈ normalizer (L : Set G) := Subgroup.le_normalizer hqL
  refine (TyDict.inducesTypeSome_two_minus_iff hL F q).2 ⟨hqN, ?_⟩
  show InvCent 192 (F.ψ ⟨q, hqL⟩)
  exact ⟨QP45_le_QA45 (F.ψ_mem _), hψsq, hψ1, hcnt⟩

end CFSG.OddStandard.SmallF3.Omega
