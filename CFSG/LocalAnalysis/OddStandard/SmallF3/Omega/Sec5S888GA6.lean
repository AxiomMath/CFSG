module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888GA5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888B2g
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Stmts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Ctx

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

theorem asc82Lemma519_of (h514 : Asc82Lemma514) (h516a : Asc82Lemma516a)
    (hpar : Asc82Lemma518Parity) (h517 : Asc82Lemma517) (h518b : Asc82Lemma518b)
    (h73 : Asc82CHdLeN) : Asc82Lemma519 := by
  classical
  intro G _ _ t L S z r B A K₁ K₂ h c q hq x hx hxN
  have hq0 := sec5b517_quad h514 c
  have hQ : Qsub K₁ K₂ h = Sec5B517Q8 hq0 := by
    rw [sec5b517_Qsub_eq, hq0.core_eq]
  have hNz := sec5b517_normalizer_le h514 c
  have hNz8 : normalizer (Sec5B517Q8 hq0 : Set G) ≤ centralizer ({z} : Set G) := by
    simpa only [hQ] using hNz
  have hperm : ∀ n ∈ normalizer (Sec5B517Q8 hq0 : Set G), ∀ i : Fin 4,
      ∃ j, CFSG.conjugate (Kfam5 K₁ K₂ h i) n = Kfam5 K₁ K₂ h j := by
    intro n hn i
    have hn' : n ∈ normalizer (Qsub K₁ K₂ h : Set G) := by simpa only [hQ] using hn
    have hmem : CFSG.conjugate (Kfam5 K₁ K₂ h i) n ∈ Gamma5 K₁ K₂ h :=
      (h517 G t L S z r B A K₁ K₂ h c).1 n hn' (Kfam5 K₁ K₂ h i)
        (by rw [sec5b517_gamma_eq]; exact ⟨i, rfl⟩)
    rw [sec5b517_gamma_eq] at hmem
    obtain ⟨j, hj⟩ := hmem
    exact ⟨j, hj.symm⟩
  have hcent : ∀ s ∈ normalizer (Sec5B517Q8 hq0 : Set G), s * s ∈ Sec5B517Q8 hq0 →
      (∀ q ∈ Sec5B517Q8 hq0, s * q * s⁻¹ * q⁻¹ ∈ zpowers z) → s ∈ Sec5B517Q8 hq0 := by
    intro s hs hss hcomm
    have hs' : s ∈ normalizer (Qsub K₁ K₂ h : Set G) := by simpa only [hQ] using hs
    have hss' : s * s ∈ Qsub K₁ K₂ h := by simpa only [hQ] using hss
    have hcomm' : ∀ q ∈ Qsub K₁ K₂ h, s * q * s⁻¹ * q⁻¹ ∈ zpowers z := by
      intro q hqQ
      exact hcomm q (by simpa only [hQ] using hqQ)
    have hmem := mem_Qsub_of_sq_mem h516a c hNz s hs' hss' hcomm'
    simpa only [hQ] using hmem
  have hparG : ∀ w ∈ normalizer (Sec5B517Q8 hq0 : Set G),
      (∀ i, CFSG.conjugate (Kfam5 K₁ K₂ h i) w = Kfam5 K₁ K₂ h i) →
      (∀ q ∈ Sec5B517Q8 hq0, w * w * q * (w * w)⁻¹ * q⁻¹ ∈ zpowers z) →
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
  have h518' : ∀ (U : Subgroup G) (n : ℕ), U ≤ normalizer (Sec5B517Q8 hq0 : Set G) →
      IsElemAbelianModSub
        (centralizerMod z (normalizer (Sec5B517Q8 hq0 : Set G)) (Sec5B517Q8 hq0)) U →
      (centralizerMod z (normalizer (Sec5B517Q8 hq0 : Set G)) (Sec5B517Q8 hq0)).relIndex U =
        2 ^ n → n ≤ 3 := by
    intro U n hU hmod hrel
    exact h518b G t L S z r B A K₁ K₂ h c n U (by simpa only [hQ] using hU)
      (by simpa only [hQ] using hmod) (by simpa only [hQ] using hrel)
  have hCd' : ∀ d : G, d ∈ Sec5B517Q8 hq0 → d * d = 1 → d ≠ 1 → d ≠ z →
      (∃ i j : Fin 4, i ≠ j ∧ d ∈ Kfam5 K₁ K₂ h i ⊔ Kfam5 K₁ K₂ h j) →
        centralizer ({d} : Set G) ⊓ centralizer ({z} : Set G) ≤
          normalizer (Sec5B517Q8 hq0 : Set G) := by
    rintro d hdQ hd2 hd1 hdz ⟨i, j, hij, hdK⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hmemΓ : ∀ k : Fin 4, Kfam5 K₁ K₂ h k ∈ Gamma5 K₁ K₂ h := fun k => by
      rw [sec5b517_gamma_eq]
      exact ⟨k, rfl⟩
    have hd : d ∈ Delta5 z (Gamma5 K₁ K₂ h) :=
      ⟨orderOf_eq_prime (by rw [pow_two]; exact hd2) hd1, hdz, Kfam5 K₁ K₂ h i, hmemΓ i,
        Kfam5 K₁ K₂ h j, hmemΓ j, hq0.ne hij, hdK⟩
    have h73d := h73 G t L S z r B A K₁ K₂ h c d hd
    simpa only [hQ] using h73d
  have hmain := lemma519_of_quad hq0 hNz8 hperm hcent hparG h518' hCd'
  have hqQ : q ∈ Sec5B517Q8 hq0 := by simpa only [hQ] using hq
  have hxN' : x⁻¹ * q * x ∈ normalizer (Sec5B517Q8 hq0 : Set G) := by
    simpa only [hQ] using hxN
  have hres := hmain q hqQ x hx hxN'
  simpa only [hQ] using hres

end CFSG.OddStandard.SmallF3.Omega
