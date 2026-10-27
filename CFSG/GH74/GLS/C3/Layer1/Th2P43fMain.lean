module

public import CFSG.GH74.GLS.C3.Layer1.Th2P43fBurn
public import CFSG.GH74.GLS.C3.Layer1.Th2P615
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P43f
  CFSG.GH74.GLS.C3.Layer1.Back

theorem b_prop43f_3b_of (hc5 : B_thm2_cent5) : B_prop43f_3b := by
  intro G _ _ hG x y K T S hs h7 hQ4 hTS hQel D hD b hbB hbx
  obtain ⟨hDP, hPK, hDel, hD4, e7, -⟩ := hD
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD2 : pRank 2 ↥D = 2 := by
    have h1 := card_eq_two_pow_pRank hDel
    rw [hD4] at h1
    have h2 : (2 : ℕ) ^ 2 = 2 ^ pRank 2 ↥D := by simpa using h1
    exact (Nat.pow_right_injective le_rfl h2).symm
  have hP2 : 2 ≤ pRank 2 ↥(T ⊓ K) := hD2.symm.le.trans (pRank_mono' hDP)
  obtain ⟨a, z, psi, F⟩ := exists_frame hc5 hG hs e7 hQ4 hTS hP2 hQel
  have hDfour : IsFourSub (T ⊓ K) D := ⟨hDP, hDel, hD4⟩
  rw [F.B_eq hDfour] at hbB ⊢
  have hfuse : FusesIn x (D ⊔ conjugate D a) := by
    by_cases hRD : conjugate (T ⊓ CxK x K) a⁻¹ = D
    · exact F.fuses_case_b hG hs e7 hP2 hQ4 hDfour (fun w hw => F.psi_R (hRD ▸ hw))
    · exact F.fuses_case_a hG hs e7 hP2 hQ4 hDfour (F.R_four hG hs e7 hP2 hQ4) rfl hRD
  exact hfuse b hbB hbx

end CFSG.GH74.GLS
