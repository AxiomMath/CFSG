module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndG3
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4EndG2

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup

variable {G : Type} [Group G]

theorem commutator_mem_zStarIn_of_invert {J T₁ : Subgroup G} (hT₁ : T₁ ≤ J) {c : G}
    (hcc : c * c = 1) (hinv : ∀ s ∈ T₁, c * s * c * s ∈ zStarIn J) {s t : G} (hs : s ∈ T₁)
    (ht : t ∈ T₁) : s⁻¹ * t⁻¹ * s * t ∈ zStarIn J := by
  have hα := hinv s hs
  have hβ := hinv t ht
  have hγ := hinv (s * t) (mul_mem hs ht)
  have h1 : (c * s * c * s)⁻¹ * (c * (s * t) * c * (s * t)) = s⁻¹ * (c * t * c * t) * t⁻¹ * s * t
      := by
    have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
    calc (c * s * c * s)⁻¹ * (c * (s * t) * c * (s * t))
        = s⁻¹ * c⁻¹ * s⁻¹ * c⁻¹ * c * s * t * c * s * t := by group
      _ = s⁻¹ * c⁻¹ * t * c * s * t := by group
      _ = s⁻¹ * (c * t * c * t) * t⁻¹ * s * t := by rw [hci]; group
  have h2 : s⁻¹ * (c * t * c * t) * t⁻¹ * s * t ∈ zStarIn J := h1 ▸ mul_mem (inv_mem hα) hγ
  have hsJ : s ∈ normalizer (J : Set G) := le_normalizer (hT₁ hs)
  have h3 : s⁻¹ * (c * t * c * t) * s⁻¹⁻¹ ∈ zStarIn J := conj_mem_zStarIn (inv_mem hsJ) hβ
  have h4 := mul_mem (inv_mem h3) h2
  rwa [show (s⁻¹ * (c * t * c * t) * s⁻¹⁻¹)⁻¹ * (s⁻¹ * (c * t * c * t) * t⁻¹ * s * t) =
    s⁻¹ * t⁻¹ * s * t by group] at h4

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem l34GraphInvertModStep_of_cover (hCov : L34GraphInvertCoverFact) :
    L34GraphInvertModStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl hcls B hBP hB8 hBZ hSN hBiff
    hAut c hcS hcc hcW hTc
  obtain ⟨-, hU3, hL34, -, hS, -, -⟩ := id hset
  obtain ⟨-, -, -, hJa, hJc, -, -⟩ := hU3
  have hcB : ∀ b ∈ B, c * b = b * c := by
    have hc : c ∈ S ⊓ centralizer (B : Set G) := by
      rw [hTc]
      exact (le_sup_right : zpowers c ≤ _) (mem_zpowers c)
    intro b hb
    exact (mem_centralizer_iff.mp (mem_inf.mp hc).2 b hb).symm
  exact hCov G J S B c (GSThmB.commutator_eq_self_of_isPComponent hJa hJc) hL34
    (GrS4.isSylowTwoIn_inf hS) hS.1 hZc hZ4 hBP hBiff hcS hcc hcW hcB

theorem l34GraphInvertStep_of_parts (hMod : L34GraphInvertModStep)
    (hGlob : L34GraphInvertGlobalStep) : L34GraphInvertStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl hcls B hBP hB8 hBZ hSN hBiff
    hAut c hcS hcc hcW hTc
  exact hGlob G a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl hcls B hBP hB8 hBZ hSN hBiff
    hAut c hcS hcc hcW hTc (hMod G a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl hcls B hBP
      hB8 hBZ hSN hBiff hAut c hcS hcc hcW hTc)

theorem l34EndGraphStep_of_parts (hCov : L34GraphInvertCoverFact)
    (hGlob : L34GraphInvertGlobalStep) (hFin : L34GraphFinalStep)
    (hTr : L34EightTransvectionFact) : L34EndGraphStep :=
  l34EndGraphStep_of_inputs (l34GraphInvertStep_of_parts (l34GraphInvertModStep_of_cover hCov)
    hGlob) hFin hTr

end CFSG.ComponentClassification.GrSLit
