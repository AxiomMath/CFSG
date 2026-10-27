
module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveOvergroupsBase

public import Certificates.Certificate19840
public import Certificates.Certificate19841
public import Certificates.Certificate19831
public import Certificates.Certificate19832

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.MaxD2
open CFSG.AGLEmbedding.FusD2 CFSG.RankThree.Native
open Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.OverD2Perm Certificates.HSOver

theorem hsON0_eq_normalizer :
    hsON0 = hs100P ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) :=
  Certificates.certificate19831.2.1

theorem card_hsON0 :
    Nat.card hsON0 = 2000 :=
  Certificates.certificate19831.2.2

theorem hs100R_normalizer_eq_Nsub :
    hs100R ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) =
      Nsub hsFiveDataR [hs100A, hs100B, hs100U] :=
  Certificates.certificate19832.2.1

theorem hs100R_normalizer_maximal :
    ∀ Y : Subgroup (Equiv.Perm (Fin 100)),
      hs100R ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) ≤ Y → Y ≤ hs100R →
      Y = hs100R ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) ∨ Y = hs100R := by
  have hM := Certificates.certificate19841
  simp only [checkMaximal, Bool.and_eq_true] at hM
  obtain ⟨⟨⟨hInv', hN'⟩, hinvN⟩, hMax⟩ := hM
  have hgi' := giT_rep (S := [hs100A, hs100B, hs100U]) (D := hsOverDataR) hsFiveDataR_hS hInv'
  have hmax := maximal_N (S := [hs100A, hs100B, hs100U]) (D := hsOverDataR) hsFiveDataR_hS hgi'
    rfl (by rw [Gsub_hsOverDataR]; exact card_hs100R) hN' hinvN hMax
  have hN2 : Nsub hsOverDataR [hs100A, hs100B, hs100U] =
      hs100R ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) := by
    have : Nsub hsOverDataR [hs100A, hs100B, hs100U] =
        Nsub hsFiveDataR [hs100A, hs100B, hs100U] := rfl
    rw [this, hs100R_normalizer_eq_Nsub]
  rw [Gsub_hsOverDataR, hN2] at hmax
  exact hmax

theorem hs100P_normalizer_overgroups :
    ∀ Y : Subgroup (Equiv.Perm (Fin 100)),
      hs100P ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) ≤ Y → Y ≤ hs100P →
      Y = hs100P ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) ∨ Y = hsOUA2 ∨
        Y = hsOUB2 ∨ Y = hs100P := by
  have h := Certificates.certificate19840
  simp only [checkOver, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hInv, hN⟩, hinvN⟩, hMax⟩ := h
  have hgi := giT_rep (S := [hs100A, hs100B]) (D := hsOverDataP) hsFiveDataP_hS hInv
  have hov := overgroups_of_check (n := 100) (S := [hs100A, hs100B]) (D := hsOverDataP) rfl
    hsFiveDataP_hS hgi rfl (by rw [hsP_closure_eq]; exact card_hs100P) hN hinvN hMax
  rw [hsP_closure_eq, nW_hsOverDataP] at hov
  have e1 : (1 :: hsOverDataP.repW.map (wordVal [hs100A, hs100B])).getD 1 1 = hsOGA := rfl
  have e2 : (1 :: hsOverDataP.repW.map (wordVal [hs100A, hs100B])).getD 2 1 = hsOGB := rfl
  rw [e1, e2, ← hsOUA2_eq_closure, ← hsOUB2_eq_closure] at hov
  rw [← hsON0_eq_normalizer]
  exact hov

end CFSG.AGLEmbeddingD2
