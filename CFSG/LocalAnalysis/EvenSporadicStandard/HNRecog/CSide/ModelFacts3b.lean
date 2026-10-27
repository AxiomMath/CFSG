module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelFacts3a

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open CFSG.EvenSporadicStandard.HNRecog.Fpf

private lemma cSideFB_exists_iff (m g : A5 × A5) :
    (∃ l : A5 × A5, sigma0 l * (sigma0 m * b0) * sigma0 g =
        sigma0 g * (sigma0 l * (sigma0 m * b0))) ↔
      ∃ h : A5 × A5, h * sigmaThetaEquiv g = g * h := by
  have hb0 : b0 * sigma0 g = sigma0 (sigmaThetaEquiv g) * b0 := by
    rw [← b0_conj_sigma0 g]
    group
  constructor
  · rintro ⟨l, hl⟩
    have hL : sigma0 l * (sigma0 m * b0) * sigma0 g =
        sigma0 (l * m) * (b0 * sigma0 g) := by
      rw [map_mul sigma0 l m]
      group
    have hR : sigma0 g * (sigma0 l * (sigma0 m * b0)) =
        sigma0 (g * (l * m)) * b0 := by
      rw [map_mul sigma0 g (l * m), map_mul sigma0 l m]
      group
    have h2 : sigma0 (l * m * sigmaThetaEquiv g) = sigma0 (g * (l * m)) := by
      rw [hL, hb0, hR] at hl
      rw [← mul_assoc] at hl
      exact (map_mul sigma0 (l * m) (sigmaThetaEquiv g)).trans (mul_right_cancel hl)
    exact ⟨l * m, sigma0_injective h2⟩
  · rintro ⟨h, hh⟩
    refine ⟨h * m⁻¹, ?_⟩
    have hmul : sigma0 (h * m⁻¹) * sigma0 m = sigma0 h := by
      rw [← map_mul sigma0 (h * m⁻¹) m]
      congr 1
      group
    have hmain : sigma0 h * b0 * sigma0 g = sigma0 g * sigma0 h * b0 := by
      calc sigma0 h * b0 * sigma0 g
          = sigma0 h * (b0 * sigma0 g) := by group
        _ = sigma0 h * (sigma0 (sigmaThetaEquiv g) * b0) := by rw [hb0]
        _ = (sigma0 h * sigma0 (sigmaThetaEquiv g)) * b0 := by group
        _ = sigma0 (h * sigmaThetaEquiv g) * b0 := by
              rw [← map_mul sigma0 h (sigmaThetaEquiv g)]
        _ = sigma0 (g * h) * b0 := by rw [hh]
        _ = (sigma0 g * sigma0 h) * b0 := by rw [map_mul sigma0 g h]
        _ = sigma0 g * sigma0 h * b0 := by group
    calc sigma0 (h * m⁻¹) * (sigma0 m * b0) * sigma0 g
        = (sigma0 (h * m⁻¹) * sigma0 m) * b0 * sigma0 g := by group
      _ = sigma0 h * b0 * sigma0 g := by rw [hmul]
      _ = sigma0 g * sigma0 h * b0 := hmain
      _ = sigma0 g * (sigma0 (h * m⁻¹) * sigma0 m) * b0 := by rw [hmul]
      _ = sigma0 g * (sigma0 (h * m⁻¹) * (sigma0 m * b0)) := by group

private lemma cSideFB_swapCent_iff (g : A5 × A5) :
    (∃ h : A5 × A5, h * sigmaThetaEquiv g = g * h) ↔
      cSideSwapCent (iota g.1, iota g.2) := by
  rw [cSideSwapCent]
  constructor
  · rintro ⟨h, hh⟩
    have h1 : iota h.1 * frobSL (iota g.2) = iota g.1 * iota h.1 := by
      have h := congrArg (fun p : A5 × A5 => iota p.1) hh
      simpa only [Prod.fst_mul, sigmaThetaEquiv_apply, map_mul,
        MulEquiv.apply_symm_apply] using h
    have h2 : iota h.2 * frobSL (iota g.1) = iota g.2 * iota h.2 := by
      have h := congrArg (fun p : A5 × A5 => iota p.2) hh
      simpa only [Prod.snd_mul, sigmaThetaEquiv_apply, map_mul,
        MulEquiv.apply_symm_apply] using h
    exact ⟨⟨iota h.1, h1⟩, ⟨iota h.2, h2⟩⟩
  · rintro ⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩
    refine ⟨(iota.symm x1, iota.symm x2), ?_⟩
    apply Prod.ext
    · apply iota.injective
      simp only [Prod.fst_mul, sigmaThetaEquiv_apply, map_mul, MulEquiv.apply_symm_apply]
      exact hx1
    · apply iota.injective
      simp only [Prod.snd_mul, sigmaThetaEquiv_apply, map_mul, MulEquiv.apply_symm_apply]
      exact hx2

theorem cSideFiveBoth_sigma0 (h : cSideModelProp) : CSideFiveBoth q0 sigma0 := by
  intro b hb g hg hg1 hg2
  obtain ⟨m, hm⟩ := exists_eq_sigma0_mul_b0 h hb
  have hiff : (∃ l : A5 × A5, sigma0 l * b * sigma0 g = sigma0 g * (sigma0 l * b)) ↔
      cSideSwapCent (iota g.1, iota g.2) := by
    rw [hm]
    exact (cSideFB_exists_iff m g).trans (cSideFB_swapCent_iff g)
  have hg5 : g ^ 5 = 1 := by
    have := pow_orderOf_eq_one g
    rwa [hg] at this
  have hg1_5 : g.1 ^ 5 = 1 := by
    have h := congrArg Prod.fst hg5
    simpa [Prod.pow_fst] using h
  have hg2_5 : g.2 ^ 5 = 1 := by
    have h := congrArg Prod.snd hg5
    simpa [Prod.pow_snd] using h
  have hG5 : (iota g.1, iota g.2) ^ 5 = 1 := by
    apply Prod.ext
    · rw [Prod.pow_fst, Prod.fst_one, ← map_pow, hg1_5, map_one]
    · rw [Prod.pow_snd, Prod.snd_one, ← map_pow, hg2_5, map_one]
  have hG1 : (iota g.1, iota g.2).1 ≠ 1 := fun hh =>
    hg1 (iota.injective (by simpa using hh))
  have hG2 : (iota g.1, iota g.2).2 ≠ 1 := fun hh =>
    hg2 (iota.injective (by simpa using hh))
  have hfix : ∀ v : V0, sigma0 g v = v ↔ actFun (iota g.1, iota g.2) v = v := by
    intro v
    simp only [sigma0_apply]
  have hmem : ∀ v : V0, v ∈ cSideFix (iota g.1, iota g.2) ↔ sigma0 g v = v := by
    intro v
    unfold cSideFix
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hfix v).symm
  constructor
  · intro hcent
    have hsc : cSideSwapCent (iota g.1, iota g.2) := hiff.mp hcent
    intro v hv
    exact h.2.2.2.2.1.1 (iota g.1, iota g.2) hG5 hG1 hG2 hsc v ((hmem v).mpr hv)
  · intro hncent
    have hnsc : ¬ cSideSwapCent (iota g.1, iota g.2) := fun hsc => hncent (hiff.mpr hsc)
    obtain ⟨hcard, hnd, hnpl⟩ :=
      h.2.2.2.2.1.2 (iota g.1, iota g.2) hG5 hG1 hG2 hnsc
    refine ⟨?_, ?_, ?_⟩
    · have e : Nat.card {v : V0 // sigma0 g v = v} =
          (Finset.univ.filter fun v : V0 => sigma0 g v = v).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      have hf : (Finset.univ.filter fun v : V0 => sigma0 g v = v) =
          cSideFix (iota g.1, iota g.2) := by
        ext v
        unfold cSideFix
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hfix v
      rw [e, hf, hcard]
    · intro v hv hvne
      obtain ⟨w, hw, hp⟩ := hnd v ((hmem v).mpr hv) hvne
      exact ⟨w, (hmem w).mp hw, by rwa [q0_polar]⟩
    · intro hpl
      obtain ⟨v, w, hv, hw, hv0, hw0, hvw, qv, qw, hpol⟩ := hpl
      exact hnpl ⟨v, (hmem v).mpr hv, w, (hmem w).mpr hw, hv0, hw0, hvw, qv, qw,
        by simpa [q0_polar] using hpol⟩

end CFSG.EvenSporadicStandard.HNRecog.CSide
