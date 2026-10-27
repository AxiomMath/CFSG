module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210NormalTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210NormalSylow

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.Open

theorem L210_normal_of_theoremA (hGold : GoldschmidtTheoremA) {X : Type} [Group X] [Finite X]
    {A : Subgroup X} (S : Sylow 2 X) (hAS : A ≤ (S : Subgroup X))
    (hSN : (S : Subgroup X) ≤ normalizer (A : Set X)) (hAb : IsElemAbelian 2 A)
    (hclosed : ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A)
    (hirr : ∀ B : Subgroup X, B ≤ A →
      (∀ n ∈ normalizer (A : Set X), ∀ b ∈ B, n * b * n⁻¹ ∈ B) → B = ⊥ ∨ B = A)
    (hcent : ∀ x ∈ normalizer (A : Set X), (∀ a ∈ A, x * a = a * x) → x ∈ A)
    (hO2 : ∀ P : Subgroup X, A ≤ P → P ≤ normalizer (A : Set X) →
      (∀ n ∈ normalizer (A : Set X), ∀ p ∈ P, n * p * n⁻¹ ∈ P) → IsPGroup 2 P → P = A)
    (hinv : ∀ B : Subgroup X, A ≤ B → B ≤ normalizer (A : Set X) →
      (∀ n ∈ normalizer (A : Set X), ∀ b ∈ B, n * b * n⁻¹ ∈ B) → B ≠ A →
        ∃ q ∈ B, q ∉ A ∧ q * q = 1)
    (hodd : ∀ P : Subgroup X, P.Normal → Odd (Nat.card P) → P = ⊥) : A.Normal := by
  let M : Subgroup X := Subgroup.normalClosure (A : Set X)
  haveI hMnormal : M.Normal := Subgroup.normalClosure_normal
  have hAM : A ≤ M := Subgroup.le_normalClosure
  have hAb' : IsMulCommutative A := hAb.1
  have hO : goldschmidtOddCore ↥M = ⊥ := goldschmidtOddCore_eq_bot_of_normal (M := M) hodd
  have hPnorm : (pCoreOf 2 M).Normal := pCoreOf_normal (M := M)
  haveI : (pCoreOf 2 M).Normal := hPnorm
  have htwo : pCoreOf 2 M = ⊥ ∨ pCoreOf 2 M = A :=
    L210_normal_two_subgroup S hSN hirr hcent hO2 (isPGroup_pCoreOf M)
  rcases htwo with hPbot | hPA
  · have hinvol : ∀ q ∈ (S : Subgroup X) ⊓ M, q * q = 1 → q ∈ A :=
      L210_thmA_involutions hGold S hAS hAb' hclosed hO hPbot
    by_cases hMN : M ⊓ normalizer (A : Set X) = A
    · have hMA : M = A :=
        L210_eq_of_burnside (M := M) hAM hAb' S hAS hSN hMN hodd
      rw [← hMA]
      exact hMnormal
    · let B : Subgroup X := M ⊓ normalizer (A : Set X)
      have hA_le_B : A ≤ B := le_inf hAM Subgroup.le_normalizer
      have hB_le_N : B ≤ normalizer (A : Set X) := inf_le_right
      have hBinv : ∀ n ∈ normalizer (A : Set X), ∀ b ∈ B, n * b * n⁻¹ ∈ B := by
        intro n hn b hb
        exact Subgroup.mem_inf.mpr
          ⟨hMnormal.conj_mem b hb.1 n, mul_mem (mul_mem hn hb.2) (inv_mem hn)⟩
      have hBne : B ≠ A := hMN
      obtain ⟨q, hqB, hqA, hq2⟩ := hinv B hA_le_B hB_le_N hBinv hBne
      have hqN : q ∈ normalizer (A : Set X) := hqB.2
      have hqM : q ∈ M := hqB.1
      obtain ⟨n, hnN, hq'S⟩ := exists_conj_mem_sylow_of_le S hSN hqN hq2
      have hq'M : n * q * n⁻¹ ∈ M := hMnormal.conj_mem q hqM n
      have hq'2 : (n * q * n⁻¹) * (n * q * n⁻¹) = 1 := by
        have h : (n * q * n⁻¹) * (n * q * n⁻¹) = n * (q * q) * n⁻¹ := by group
        rw [h, hq2, mul_one, mul_inv_cancel]
      have hq'A : n * q * n⁻¹ ∈ A :=
        hinvol (n * q * n⁻¹) (Subgroup.mem_inf.mpr ⟨hq'S, hq'M⟩) hq'2
      have hqA' : n⁻¹ * (n * q * n⁻¹) * n ∈ A :=
        (Subgroup.mem_normalizer_iff''.mp hnN (n * q * n⁻¹)).mp hq'A
      have hqA'' : q ∈ A := by
        rw [show n⁻¹ * (n * q * n⁻¹) * n = q by group] at hqA'
        exact hqA'
      exact absurd hqA'' hqA
  · rw [← hPA]
    exact hPnorm

end CFSG.EvenSporadicStandard.HNRecog.Harada
