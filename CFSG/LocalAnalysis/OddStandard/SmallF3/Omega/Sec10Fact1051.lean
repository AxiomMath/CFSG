module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10F1051Frame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactPockets
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Inputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PocketsSup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelF1051Cnt

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

local notation "z0" => Certificates.OmegaT0.z0 ()

theorem asc82Fact1051_of_pockets
    (hP5 : Asc82FactPockets5) : Asc82Fact1051 := by
  intro G _ _ L P S t z K1 K2 U hL hP hPS hSN hS2 ht2 htC hSt hzP hz2 hSz hK1 hK2 hne hWU hUS
    hCU hel n hn hidx
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
  have hQL : secQ K1 K2 ≤ L := (twoCoreIn_le_self (K1 ⊔ K2)).trans hXL
  have htsq : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h
  have htne : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    omega
  have hUN : U ≤ normalizer (L : Set G) := hUS.trans hSN
  have hS : F.Setup1051 t (secQ K1 K2) U Q32 :=
    { Q_le_L := hQL, img_Q := hQ, t_sq := htsq, t_ne := htne, t_cent := htC, U_le_N := hUN,
      W_le_U := hWU, cent_U := hCU }
  have hUA : hS.phiU.range ≤ QA45.originalSubgroup := by
    rintro _ ⟨u, rfl⟩
    exact F.mem_A _
  have hUz : ∀ x ∈ hS.phiU.range, x * z0 = z0 * x := by
    rintro _ ⟨⟨u, hu⟩, rfl⟩
    rw [← hψz]
    exact (F.comm_phi_psi_iff ⟨u, hUN hu⟩ zL).2 (hSz u (hUS hu))
  have hQU : Q32 ≤ hS.phiU.range := by
    intro q hq
    obtain ⟨l, hlQ, hl⟩ := hS.exists_of_mem_Qm hq
    exact ⟨⟨(l : G), hWU (Subgroup.mem_sup_left hlQ)⟩, hl⟩
  have hel' : ∀ a ∈ hS.phiU.range, ∀ b ∈ hS.phiU.range,
      a * b * a⁻¹ * b⁻¹ ∈ Q32 ∧ a * a ∈ Q32 := by
    rintro _ ⟨⟨u, hu⟩, rfl⟩ _ ⟨⟨v, hv⟩, rfl⟩
    obtain ⟨h1, h2⟩ := hel u hu v hv
    have huN := hUN hu
    have hvN := hUN hv
    have hcN : u * v * u⁻¹ * v⁻¹ ∈ normalizer (L : Set G) :=
      (normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).mul_mem
        ((normalizer (L : Set G)).mul_mem huN hvN) ((normalizer (L : Set G)).inv_mem huN))
        ((normalizer (L : Set G)).inv_mem hvN)
    have hsN : u * u ∈ normalizer (L : Set G) := (normalizer (L : Set G)).mul_mem huN huN
    refine ⟨?_, ?_⟩
    · have h3 := hS.phi_mem h1 hcN
      rw [F.phi_commutator huN hvN hcN] at h3
      exact h3
    · have h3 := hS.phi_mem h2 hsN
      rw [F.phi_mul_self huN hsN] at h3
      exact h3
  obtain ⟨hn2, hlt⟩ := model1051 hUA hUz hQU hel' hn (by rw [hS.relIndex_phiU]; exact hidx)
  refine ⟨hn2, ?_⟩
  have h1 := hS.card_dset_le zL hψz
  have h2 : 2 * 2 ^ 5 ≤ Nat.card ↥(secW t K1 K2) := by
    rw [← card_Q32]
    exact hS.two_mul_card_le
  show 2 ^ n * Nat.card {w : G // w ∈ secQ K1 K2 ⊔ zpowers t ∧
    ∀ u ∈ U, w * u * w⁻¹ * u⁻¹ ∈ zpowers (zL : G)} < Nat.card ↥(secW t K1 K2)
  calc 2 ^ n * Nat.card {w : G // w ∈ secQ K1 K2 ⊔ zpowers t ∧
        ∀ u ∈ U, w * u * w⁻¹ * u⁻¹ ∈ zpowers (zL : G)}
      ≤ 2 ^ n * (Nat.card {q : P45 // q ∈ Q32 ∧
        ∀ x ∈ hS.phiU.range, q * x * q⁻¹ * x⁻¹ ∈ zpowers z0} * 2) := Nat.mul_le_mul_left _ h1
    _ = 2 * (2 ^ n * Nat.card {q : P45 // q ∈ Q32 ∧
        ∀ x ∈ hS.phiU.range, q * x * q⁻¹ * x⁻¹ ∈ zpowers z0}) := by ring
    _ < 2 * 32 := by omega
    _ ≤ Nat.card ↥(secW t K1 K2) := by omega

theorem asc82Fact1051_of_cert :
    Asc82Fact1051 :=
  asc82Fact1051_of_pockets asc82FactPockets5_of_cert

end CFSG.OddStandard.SmallF3.Omega
