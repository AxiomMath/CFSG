module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888B6a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888B2g
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Stmts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Ctx

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82SylowContain_of (h514 : Asc82Lemma514) (h516a : Asc82Lemma516a)
    (hpar : Asc82Lemma518Parity) (h517 : Asc82Lemma517) : Asc82SylowContain := by
  classical
  intro G _ _ t L S z r B A K₁ K₂ h c T hQT hTN
  have hq := sec5b517_quad h514 c
  have hQ : Qsub K₁ K₂ h = Sec5B517Q8 hq := by
    rw [sec5b517_Qsub_eq, hq.core_eq]
  have hNz := sec5b517_normalizer_le h514 c
  have hNz8 : normalizer (Sec5B517Q8 hq : Set G) ≤ centralizer ({z} : Set G) := by
    simpa only [hQ] using hNz
  have hQT' : Sec5B517Q8 hq ≤ T := by simpa only [hQ] using hQT
  have hTN' : IsSylow2Of T (normalizer (Sec5B517Q8 hq : Set G)) := by
    simpa only [hQ] using hTN
  have hperm : ∀ n ∈ normalizer (Sec5B517Q8 hq : Set G), ∀ i : Fin 4,
      ∃ j, CFSG.conjugate (Kfam5 K₁ K₂ h i) n = Kfam5 K₁ K₂ h j := by
    intro n hn i
    have hn' : n ∈ normalizer (Qsub K₁ K₂ h : Set G) := by simpa only [hQ] using hn
    have hmem : CFSG.conjugate (Kfam5 K₁ K₂ h i) n ∈ Gamma5 K₁ K₂ h :=
      (h517 G t L S z r B A K₁ K₂ h c).1 n hn' (Kfam5 K₁ K₂ h i)
        (by rw [sec5b517_gamma_eq]; exact ⟨i, rfl⟩)
    rw [sec5b517_gamma_eq] at hmem
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, hj.symm⟩
  have hcent : ∀ s ∈ normalizer (Sec5B517Q8 hq : Set G), s * s ∈ Sec5B517Q8 hq →
      (∀ q ∈ Sec5B517Q8 hq, s * q * s⁻¹ * q⁻¹ ∈ zpowers z) → s ∈ Sec5B517Q8 hq := by
    intro s hs hss hcomm
    have hs' : s ∈ normalizer (Qsub K₁ K₂ h : Set G) := by simpa only [hQ] using hs
    have hss' : s * s ∈ Qsub K₁ K₂ h := by simpa only [hQ] using hss
    have hcomm' : ∀ q ∈ Qsub K₁ K₂ h, s * q * s⁻¹ * q⁻¹ ∈ zpowers z := by
      intro q hqQ
      exact hcomm q (by simpa only [hQ] using hqQ)
    have hmem := mem_Qsub_of_sq_mem h516a c hNz s hs' hss' hcomm'
    simpa only [hQ] using hmem
  have hparG : ∀ w ∈ normalizer (Sec5B517Q8 hq : Set G),
      (∀ i, CFSG.conjugate (Kfam5 K₁ K₂ h i) w = Kfam5 K₁ K₂ h i) →
      (∀ q ∈ Sec5B517Q8 hq, w * w * q * (w * w)⁻¹ * q⁻¹ ∈ zpowers z) →
        Even (Nat.card {i : Fin 4 // ∃ q ∈ twoCoreIn (Kfam5 K₁ K₂ h i),
          w⁻¹ * q * w ≠ q ∧ w⁻¹ * q * w ≠ q * z}) := by
    intro w hw hwfix hww
    have hw' : w ∈ normalizer (Qsub K₁ K₂ h : Set G) := by simpa only [hQ] using hw
    have hmod : w * w ∈ centralizerMod z (normalizer (Qsub K₁ K₂ h : Set G))
        (Qsub K₁ K₂ h) := by
      refine ⟨mul_mem hw' hw', hNz (mul_mem hw' hw'), mul_mem hw' hw', ?_⟩
      intro q hqQ
      exact hww q (by simpa only [hQ] using hqQ)
    exact hpar G t L S z r B A K₁ K₂ h c w hw' hwfix hmod
  exact isSylow2Of_centralizer_of_quad hq hNz8 hperm hcent hparG hQT' hTN'

end CFSG.OddStandard.SmallF3.Omega
