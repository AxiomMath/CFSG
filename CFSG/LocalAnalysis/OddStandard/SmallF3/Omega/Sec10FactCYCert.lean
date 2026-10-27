module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Fact107c
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactCYAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactCYSplit
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FactsCCert
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109CInputs
public import Certificates.Certificate442006
public import Certificates.Certificate442018

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

local notation "z0" => Certificates.OmegaT0.z0 ()

theorem asc82FactCY_of_pockets
    (hP5 : Asc82FactPockets5) : Asc82FactCY := by
  intro G _ _ t L S z K1 K2 hctx hL hSN hCS hP r hrS hrord hrty hne hnorm s hsN hss hsz hst hA
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have hK1 := hctx.pocket1
  have hK2 := hctx.pocket2
  have hzL : z ∈ L := (Subgroup.mem_inf.1 (hK1.2.1 hK1.1)).1
  have hzS : z ∈ S := hctx.mem_S
  have hzP : z ∈ centerIn (S ⊓ L) :=
    mem_centerIn_iff.2 ⟨Subgroup.mem_inf.2 ⟨hzS, hzL⟩, fun y hy =>
      (hctx.central y (Subgroup.mem_inf.1 hy).1).symm⟩
  obtain ⟨F, hFP, hQL, hQ⟩ := exists_frame_Q32 hP5 hL hP hzP hz2 hK1 hK2 hctx.ne
  have hSet := PspFrame.Setup107.of_ctx hctx hSN hCS
  have hN := hSet.S_le_N
  have hr2 : r * r = 1 := by
    have h := pow_orderOf_eq_one r
    rwa [hrord, pow_two] at h
  have hz1 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz2, pow_two] at h
  have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  obtain ⟨hrN, hinv⟩ := (TyDict.inducesTypeSome_four_minus_iff hL F r).1 hrty
  have hrP : F.phiG r ∉ QP45.originalSubgroup := by
    rw [F.phiG_of_mem hrN]
    intro hmem
    have := (MoInv.mem_P_iff_of_invCent hinv).1 hmem
    omega
  have hrT0 : F.phiG r ∉ QT0.originalSubgroup := fun hh => hrP (X11.QT0_le hh)
  obtain ⟨hA2S, hA2e, hA2n⟩ := (hnorm (secA2 t r K1 K2)).2 (Or.inr rfl)
  obtain ⟨B2, y2, hM, -⟩ := hSet.exists_r hFP hQL hQ hA2S hA2e hne
  obtain ⟨-, hcard2, hpre2, hcomm2, hsq2⟩ := hSet.e32_data (F := F) hA2S hA2e
  have himg2 : F.imgS S (secA2 t r K1 K2) = B2 := by
    rcases hM.normal_elem _ (hSet.imgS_mono (F := F) hA2S) hcomm2 hsq2 hcard2
      (hSet.normal_imgS hA2n) with he | he
    · exact absurd (by rw [← hpre2, he, hSet.secA_eq hFP]) hne
    · exact he
  have hA2pre : secA2 t r K1 K2 = F.preS S B2 := by rw [← himg2, hpre2]
  have hAeq : ∀ y : ↥S, (y : G) ∈ secA t S L ↔ F.phiG (y : G) ∈ B0 := fun y => by
    rw [hSet.secA_eq hFP, F.mem_preS hN]
    exact ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩
  have hA2eq : ∀ y : ↥S, (y : G) ∈ secA2 t r K1 K2 ↔ F.phiG (y : G) ∈ B2 := fun y => by
    rw [hA2pre, F.mem_preS hN]
    exact ⟨fun h => h.2, fun h => ⟨y.2, h⟩⟩
  have hrim : F.phiG r ∈ F.imgS S S := (F.mem_imgS hN).2 ⟨r, hrS, hrS, rfl⟩
  have hT0S := hSet.T0_le_imgS hFP
  have hSA := hSet.imgS_le_A (F := F) S
  have hS2 := hSet.isPGroup_imgS (F := F) (le_refl S)
  obtain ⟨B2', y2', hM'⟩ := Certificates.certificate442006.model _ hT0S hSA hS2 _ hrim hrT0
  have hB2 : B2 = B2' := hM'.normal_elem B2 hM.le hM.comm hM.sq hM.card hM.normal
    fun h => hM.y2_out (h hM.y2_mem)
  rw [← hB2] at hM'
  have hψz : F.ψ ⟨z, hzL⟩ = z0 := by
    have h1 : F.ψ ⟨z, hzL⟩ ∈ F.img (centerIn (S ⊓ L)) := PspFrame.psi_mem_img.2 hzP
    rw [F.img_centerIn inf_le_right, hFP] at h1
    rcases eq_z0_of_mem_centerIn h1 with h | h
    · exfalso
      have h3 := F.orderOf_psi ⟨z, hzL⟩
      rw [h, orderOf_one] at h3
      have h4 : orderOf ((⟨z, hzL⟩ : ↥L) : G) = 2 := hz2
      omega
    · exact h
  have hφz : F.phiG z = z0 := (F.phiG_psi ⟨z, hzL⟩).trans hψz
  obtain ⟨Φ, hΦinj, hΦ1, hΦt, hΦL, hΦlift⟩ := hSet.exists_split hFP hrS hr2 hrT0
  have hΦz : Φ ⟨z, hzS⟩ = (z0, 1) :=
    Prod.ext (by rw [hΦ1]; exact hφz) (hΦL ⟨z, hzS⟩ hzL)
  have hB0le : B0 ≤ F.imgS S S := hSet.B0_le_imgS hFP
  have hrange : ∀ g, g ∈ B0.prod ⊤ ∨ g ∈ B2.prod ⊤ → ∃ y : ↥S, Φ y = g := by
    rintro ⟨p, e⟩ hg
    have hp : p ∈ F.imgS S S := by
      rcases hg with hg | hg
      · exact hB0le (Subgroup.mem_prod.1 hg).1
      · exact hM.le (Subgroup.mem_prod.1 hg).1
    exact hΦlift p hp e
  obtain ⟨α, hαc, hα⟩ := exists_conj_invol hsN hss
  have h0 : α ⟨t, hSet.t_mem⟩ = ⟨t, hSet.t_mem⟩ * ⟨z, hzS⟩ := by
    apply Subtype.ext
    rw [hαc]
    show s * t * s = t * z
    rw [hs1] at hst
    exact hst
  have h1 : α ⟨z, hzS⟩ = ⟨z, hzS⟩ := by
    apply Subtype.ext
    rw [hαc]
    show s * z * s = z
    rw [hsz, mul_assoc, hss, mul_one]
  have hαA : ∀ y : ↥S, (y : G) ∈ secA t S L → ((α y : ↥S) : G) ∈ secA2 t r K1 K2 := by
    intro y hy
    have h := hA y hy
    rw [hs1] at h
    rw [hαc]
    exact h
  have hcardA : Nat.card ↥(secA2 t r K1 K2) ≤ Nat.card ↥(secA t S L) := by
    rw [hA2e.2, hSet.card_secA hFP]
  have hαA2 : ∀ y : ↥S, (y : G) ∈ secA2 t r K1 K2 → ((α y : ↥S) : G) ∈ secA t S L := by
    intro y hy
    have h := conj_swap hss hA hcardA y hy
    rw [hs1] at h
    rw [hαc]
    exact h
  have h02 : ∀ y : ↥S, Φ y ∈ B0.prod ⊤ → Φ (α y) ∈ B2.prod ⊤ := by
    intro y hy
    refine Subgroup.mem_prod.2 ⟨?_, Subgroup.mem_top _⟩
    have h1 : F.phiG ((y : ↥S) : G) ∈ B0 := by
      rw [← hΦ1]
      exact (Subgroup.mem_prod.1 hy).1
    rw [hΦ1]
    exact (hA2eq _).1 (hαA _ ((hAeq _).2 h1))
  have h20 : ∀ y : ↥S, Φ y ∈ B2.prod ⊤ → Φ (α y) ∈ B0.prod ⊤ := by
    intro y hy
    refine Subgroup.mem_prod.2 ⟨?_, Subgroup.mem_top _⟩
    have h1 : F.phiG ((y : ↥S) : G) ∈ B2 := by
      rw [← hΦ1]
      exact (Subgroup.mem_prod.1 hy).1
    rw [hΦ1]
    exact (hAeq _).1 (hαA2 _ ((hA2eq _).2 h1))
  obtain ⟨y, hu2, hu1, huz⟩ := Certificates.certificate442018 _ B0 B2 y2' hT0S hSA hS2
    ⟨_, hrim, hrT0⟩ hM' B0_le_T0 (fun a ha b hb => B0_comm ha hb) (by rw [card_B0]; norm_num)
    ↥S Φ hΦinj α hα _ _ hΦt hΦz h0 h1 hrange h02 h20
  have key : ((y⁻¹ * α y : ↥S) : G) = (y : G)⁻¹ * s * (y : G) * s := by
    show (y : G)⁻¹ * ((α y : ↥S) : G) = _
    rw [hαc]
    simp only [mul_assoc]
  refine ⟨(y : G), y.2, ?_, ?_⟩
  · have h := congrArg Subtype.val hu2
    rw [Subgroup.coe_mul, key, Subgroup.coe_one] at h
    exact h
  · intro hmem
    rw [← key] at hmem
    rcases (mem_zpowers_of_sq hz1).1 hmem with h | h
    · exact hu1 (Subtype.ext h)
    · exact huz (Subtype.ext h)

theorem asc82FactCY_of_cert :
    Asc82FactCY :=
  asc82FactCY_of_pockets asc82FactPockets5_of_cert

theorem asc82FactsC_of_cert :
    Asc82FactsC :=
  asc82FactsC_of_cy asc82FactCY_of_cert

end CFSG.OddStandard.SmallF3.Omega
