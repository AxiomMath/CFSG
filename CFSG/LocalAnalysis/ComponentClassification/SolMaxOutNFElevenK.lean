module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutNFAlt
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutNFFormEleven

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem signalizerCaseOneConjugateElevenFormInput_of_kernelForm
    (hD2 : SignalizerConjKernelExclusion)
    (hKF : SignalizerCaseOneConjugateOutsideKernelFormInput) :
    SignalizerCaseOneConjugateElevenFormInput := by
  intro X _ _ _ t J e E D S hW M hMH hMpc hJM hHN hsup θ ρ hρ Q hQK hQ2 hQcard htQ hA hNT a g
    ha hgH hs hsNQ hσ2 hσ1 x hxM hxo hx2 hx4 hxf hx'
  have hn9 := S.nine_le
  have hx'2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  by_cases hx'M : g * x * g⁻¹ ∈ M
  · have hCx := hA x hxM hx2 hx4
    have hxno : x ∉ oddGen (centralizer ({x} : Set X)) :=
      not_mem_oddGen_of_four (le_normalizer hxM) hx2 hx4 (hCx.trans hHN)
    have hx'o : g * x * g⁻¹ ∉ oddGen (centralizer ({g * x * g⁻¹} : Set X)) := by
      intro h
      have h1 := conj_mem_oddGen_centralizer (g := g⁻¹) h
      have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rw [h2] at h1
      exact hxno h1
    have hx1 : x ≠ 1 := by
      rintro rfl
      have h1 : ρ ⟨1, le_normalizer hxM⟩ = 1 := map_one ρ
      rw [h1, Perm.support_one, Finset.card_empty] at hx4
      omega
    have hx'1 : g * x * g⁻¹ ≠ 1 := by
      intro h
      apply hx1
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have h4 := hρ.card_support_eq_four_of_not_mem_oddGen (by omega) hx'M hx'2 hx'1 hx'o
    exact ⟨h4, hA _ hx'M hx'2 h4⟩
  · exfalso
    have hs2 := S.mul_self_eq_one_of_conjugate hD2 hMH hMpc hHN hsup hρ hQK hQ2 hQcard hA hNT ha hs
      hsNQ hσ2 hσ1
    by_cases h5 : 5 ≤ 11 - (ρ ⟨g * x * g⁻¹, hHN hx'⟩).support.card
    · exact S.false_of_conjugate_outside_of_five hD2 (by norm_num) hMH hMpc hHN hsup hρ hQK hQ2
        hQcard hA hNT ha hgH hs hsNQ hσ2 hσ1 hxM hxo hx2 hx4 hx' h5
    · have ha1 : a ≠ 1 := by
        rintro rfl
        apply hσ1
        have h1 : (⟨g⁻¹ * 1 * g, hHN hs⟩ : ↥(normalizer (M : Set X))) = 1 :=
          Subtype.ext (show g⁻¹ * 1 * g = 1 by group)
        rw [h1, map_one]
      have hcard : (ρ ⟨g * x * g⁻¹, hHN hx'⟩).support.card ≤ 11 := by
        have := Finset.card_le_univ (ρ ⟨g * x * g⁻¹, hHN hx'⟩).support
        rwa [Fintype.card_fin] at this
      have hev : 2 ∣ (ρ ⟨g * x * g⁻¹, hHN hx'⟩).support.card := by
        refine Perm.two_dvd_card_support ?_
        rw [sq, ← map_mul]
        have h1 : (⟨g * x * g⁻¹, hHN hx'⟩ : ↥(normalizer (M : Set X))) * ⟨g * x * g⁻¹, hHN hx'⟩ =
            1 := Subtype.ext hx'2
        rw [h1, map_one]
      obtain ⟨q, hq⟩ := hev
      obtain ⟨y, hyM, hy2, hyx', hρy, hyo, hko, hCk⟩ := exists_kernel_involution hMH hMpc hHN
        (by omega) hρ hQK hQ2 hQcard hNT ha ha1 hxo hx2 hx' hx'M (by omega)
      exact hKF X t J 11 e E D S (by norm_num) hW M hMH hMpc hJM hHN hsup θ ρ hρ Q hQK hQ2 hQcard
        htQ hA hNT a g ha hgH hs hsNQ hσ2 hσ1 x hxM hxo hx2 hx4 hxf hx' hx'M hs2 (by omega) y hyM
        hy2 hyx' hρy hyo hko hCk

theorem signalizerTrivialityInput_of_residues_alt_eleven
    (hmax : SolAltLit.MaximalAltComponentInput) (hbal : Sol78.BalanceTwoComponentInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hsmall : SignalizerSmallDegreeInput) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hSwap : SignalizerSwapAltExclusion)
    (hGT : Sol78.StronglyClosedResidualInput) (hA : SignalizerClaimASmallInput)
    (h2 : SignalizerCaseTwoFinishInput) (hMult : TBLit.HeldTrivialMultiplier)
    (hAlt : SignalizerCaseOneConjugateOutsideAltInput) (h9 : SignalizerNineInput) :
    SolAltLit.SignalizerTrivialityInput :=
  signalizerTrivialityInput_of_residues_alt hmax hbal hPump hN1 hsmall hT13 hML hSch hSwap hGT hA
    h2 hAlt
    (signalizerCaseOneStrongClosureElevenInput_of_conjugateForm
      (balanceLemmaInput_of_smallDegree hbal hPump hN1 hsmall)
      (signalizerLemma35_of_smallDegree hbal hPump hN1 hsmall) hT13 hML hSch hPump hN1 hMult
      (signalizerCaseOneConjugateElevenFormInput_of_kernelForm
        (signalizerConjKernelExclusion_of_inputs
          (balanceLemmaInput_of_smallDegree hbal hPump hN1 hsmall)
          (signalizerLemma35_of_smallDegree hbal hPump hN1 hsmall) hT13 hML hSch)
        (signalizerCaseOneConjugateOutsideKernelFormInput_of_alt hAlt))) h9

end CFSG.ComponentClassification.SolMax
