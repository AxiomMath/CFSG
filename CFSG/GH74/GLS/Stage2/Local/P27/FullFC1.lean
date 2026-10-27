module

public import CFSG.GH74.GLS.Stage2.Local.P27.S45E
import CFSG.GH74.GLS.AssemblyComponents

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

theorem cxK_le_sup {G : Type} [Group G] [Finite G] {x : G} {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hE : HasNormal2Compl (CxK x (Jx x))) :
    CxK x (Jx x) ≤ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hNC, hNn, hNodd, a, ha⟩ := hE
  have hC₁C : CxK x (Jx x) ≤ centralizer ({x} : Set G) := S45.CxK_Jx_le x
  have hC₁nor : ((CxK x (Jx x)).subgroupOf (centralizer ({x} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hC₁C).2 (S45.centralizer_le_normalizer_CxK_Jx x)
  have hNO : N ≤ pPrimeCoreOf 2 (centralizer ({x} : Set G)) := by
    have hN1 : N ≤ pPrimeCoreOf 2 N := by
      have h : (⊤ : Subgroup ↥N) ≤ pPrimeCore 2 ↥N :=
        le_sSup ⟨inferInstance, by simpa using Nat.coprime_two_left.2 hNodd⟩
      intro n hn
      exact ⟨⟨n, hn⟩, h (Subgroup.mem_top _), rfl⟩
    exact hN1.trans ((pPrimeCoreOf_le_of_normal 2 hNC hNn).trans
      (pPrimeCoreOf_le_of_normal 2 hC₁C hC₁nor))
  have hP : IsSylowOf 2 (T ⊓ CxK x (Jx x)) (CxK x (Jx x)) :=
    hT.inf_of_le_normalizer hC₁C (S45.centralizer_le_normalizer_CxK_Jx x)
  have hsup : CxK x (Jx x) ≤ N ⊔ (T ⊓ CxK x (Jx x)) := by
    rw [← Subgroup.relIndex_eq_one]
    have h0 : N.relIndex (CxK x (Jx x)) = 2 ^ a := ha
    have h1 : (N ⊔ (T ⊓ CxK x (Jx x))).relIndex (CxK x (Jx x)) ∣ 2 ^ a := by
      rw [← h0]
      exact Subgroup.relIndex_dvd_of_le_left (CxK x (Jx x)) le_sup_left
    have h2 : (N ⊔ (T ⊓ CxK x (Jx x))).relIndex (CxK x (Jx x)) ∣
        (T ⊓ CxK x (Jx x)).relIndex (CxK x (Jx x)) :=
      Subgroup.relIndex_dvd_of_le_left (CxK x (Jx x)) le_sup_right
    have h3 : ¬ 2 ∣ (T ⊓ CxK x (Jx x)).relIndex (CxK x (Jx x)) := (isSylowOf_iff.1 hP).2.2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk, hk0, pow_zero]
    · exact absurd ((dvd_pow_self 2 hkpos.ne').trans (hk ▸ h2)) h3
  exact hsup.trans (sup_le_sup hNO inf_le_left)

end CFSG.GH74.GLS.Stage2.Local.P27
