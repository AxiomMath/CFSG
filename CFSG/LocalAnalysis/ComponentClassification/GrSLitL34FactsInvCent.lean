module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInvCentModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverInvModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInner
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOuter

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.ComponentClassification.UnbalancedLayer

theorem l34InvolutionCentralizerFact :
    L34InvolutionCentralizerFact := by
  intro G _ _ K t hK hL ht2 htN
  by_cases htW : t ∈ withKernel K
  · obtain ⟨e₀, he₀⟩ := exists_inner htW htN
    have he₀2 : e₀ * e₀ ∈ center (Jhat K) := by
      rw [mem_center_iff]
      intro g
      have h1 := betaHat_betaHat K htN ht2 g
      rw [he₀, he₀] at h1
      calc g * (e₀ * e₀) = (e₀ * e₀) * (e₀⁻¹ * (e₀⁻¹ * g * e₀) * e₀) := by group
        _ = (e₀ * e₀) * g := by rw [h1]
    obtain ⟨q, l, hQ, hq⟩ := exists_inner_frame hK hL he₀2
    have hw2 : ilift l (8, 1, 0, 0) * ilift l (8, 1, 0, 0) = 1 :=
      hQ.ilift_mul_self (by decide)
    have hq8 : q (ilift l (8, 1, 0, 0)) = wordPerm (tg 8) := hQ.q_ilift (by norm_num)
    have hwc := hQ.comm_i8 hq
    have hfix : betaHat K htN (ilift l (8, 1, 0, 0)) = ilift l (8, 1, 0, 0) := by
      rw [he₀, mul_assoc, ← hwc, ← mul_assoc, inv_mul_cancel, one_mul]
    obtain ⟨w, hwK, hww, hwt, hwe⟩ := exists_fixed_involution_lift htN ht2 hw2 hfix
    have h80 : wordPerm (tg 8) ≠ 1 := fun h => by
      rw [← wordPerm_tg_zero] at h
      exact absurd (tg_injective (by norm_num) (by norm_num) h) (by norm_num)
    refine ⟨w, hwK, hww, hwt, fun hz => ?_, fun hk => ?_⟩
    · have h1 := (mem_zStarIn_iff hwK).1 hz
      rw [hwe hwK, ← hQ.ker, MonoidHom.mem_ker, hq8] at h1
      exact h80 h1
    · have hkN := (mem_coreActionKernel.mp hk).1
      have hwN : w ∈ normalizer (K : Set G) := le_normalizer hwK
      have hβ : ∀ e, e₀⁻¹ * e * e₀ =
          (ilift l (8, 1, 0, 0))⁻¹ * e * ilift l (8, 1, 0, 0) := by
        intro e
        rw [← he₀, betaHat_congr K htN (mul_mem hwN hkN) (by group), betaHat_mul K hwN hkN,
          betaHat_of_mem_coreActionKernel hk hkN, betaHat_of_mem hwK hwN, hwe hwK]
      have hc : ilift l (8, 1, 0, 0) * e₀⁻¹ ∈ q.ker := by
        rw [hQ.ker, mem_center_iff]
        intro g
        calc g * (ilift l (8, 1, 0, 0) * e₀⁻¹) = ilift l (8, 1, 0, 0) *
            ((ilift l (8, 1, 0, 0))⁻¹ * g * ilift l (8, 1, 0, 0)) * e₀⁻¹ := by group
          _ = ilift l (8, 1, 0, 0) * (e₀⁻¹ * g * e₀) * e₀⁻¹ := by rw [hβ g]
          _ = ilift l (8, 1, 0, 0) * e₀⁻¹ * g := by group
      rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one, hq8] at hc
      rcases hq with h | h
      · exact h80 (hc.trans h)
      · rw [h] at hc
        exact absurd (tg_injective (by norm_num) (by norm_num) hc) (by norm_num)
  · obtain ⟨q, hqS, hqsurj, hqker, h3, ρ, hρ, hβ⟩ :=
      exists_outer_realization hK hL htN ht2 htW
    obtain ⟨l, hl, hls⟩ := exists_lam (commutator_jhat hK) q hqS hqsurj (hqker ▸ le_refl _)
    have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
    obtain ⟨ŵ, hfix, hw2, hq1⟩ := hQ.exists_witness hρ hβ
    obtain ⟨w, hwK, hww, hwt, hwe⟩ := exists_fixed_involution_lift htN ht2 hw2 hfix
    refine ⟨w, hwK, hww, hwt, fun hz => ?_, fun hk => ?_⟩
    · have h1 := (mem_zStarIn_iff hwK).1 hz
      rw [hwe hwK, ← hqker, MonoidHom.mem_ker] at h1
      exact hq1 h1
    · apply htW
      rw [show t = w * (w⁻¹ * t) by group]
      exact mul_mem (mem_sup_left hwK) (mem_sup_right hk)

end CFSG.ComponentClassification.GrSLit.L34Facts
