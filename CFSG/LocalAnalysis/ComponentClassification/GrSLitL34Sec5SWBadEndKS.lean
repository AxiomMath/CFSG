module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWBadF
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWBadUn
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWBadUnKS
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer

section Fusion

theorem l34Lemma43FusionStepKS_of_bad (hBad : L34Lemma43BadFusionStepKS) :
    L34Lemma43FusionStepKS := by
  intro G _ _ a x J S A hset hcent hrun h3 W hW hWodd hWB hNJ K hKM hKc hsup hKN hSM hSyl g
    hg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hU3, hL34, -, hS, haS, -⟩ := id hset
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJper : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJa hU3.2.2.2.2.1
  have ha2 : orderOf a = 2 := hU3.1
  have haK : a ∈ coreActionKernel J := GrS4.mem_coreActionKernel_of_le_centralizer hJa
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hS
  have hy2 : IsPGroup 2 (zpowers (g⁻¹ * a * g)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective a
    simpa [MulAut.conj_apply, ha2] using this
  obtain ⟨m₁, hm₁M, hm₁⟩ := GrS4.exists_conj_mem_of_isSylowTwoIn hSM (zpowers_le.mpr hg) hy2
  have hbS : (g * m₁)⁻¹ * a * (g * m₁) ∈ S := by
    have := hm₁ _ (mem_zpowers _)
    rwa [show m₁⁻¹ * (g⁻¹ * a * g) * m₁ = (g * m₁)⁻¹ * a * (g * m₁) by group] at this
  suffices hmain : ∃ m ∈ normalizer (W : Set G), (g * m₁)⁻¹ * a * (g * m₁) = m⁻¹ * a * m by
    obtain ⟨m, hm, hbm⟩ := hmain
    refine ⟨m * m₁⁻¹, mul_mem hm (inv_mem hm₁M), ?_⟩
    calc g⁻¹ * a * g = m₁ * ((g * m₁)⁻¹ * a * (g * m₁)) * m₁⁻¹ := by group
      _ = (m * m₁⁻¹)⁻¹ * a * (m * m₁⁻¹) := by rw [hbm]; group
  generalize g * m₁ = k at hbS ⊢
  by_cases hka : k⁻¹ * a * k = a
  · exact ⟨1, one_mem _, by rw [hka]; group⟩
  by_cases hkK : k⁻¹ * a * k ∈ withKernel J
  · exact exists_conj_of_mem_withKernel hset hcent h3 hWB hNJ hSyl hbS hkK
  obtain ⟨c, hc, E, hES, hE, hbE, haE, -, hE4⟩ := exists_eight_of_conj hset hcent hbS hka
  have hcN : c ∈ normalizer (J : Set G) := (mem_inf.mp hc).1
  have hkc : (k * c)⁻¹ * a * (k * c) = c⁻¹ * (k⁻¹ * a * k) * c := by group
  suffices hmain : ∃ m ∈ normalizer (W : Set G), (k * c)⁻¹ * a * (k * c) = m⁻¹ * a * m by
    obtain ⟨m, hm, hbm⟩ := hmain
    refine ⟨m * c⁻¹, mul_mem hm (hNJ (inv_mem hcN)), ?_⟩
    calc k⁻¹ * a * k = c * ((k * c)⁻¹ * a * (k * c)) * c⁻¹ := by group
      _ = (m * c⁻¹)⁻¹ * a * (m * c⁻¹) := by rw [hbm]; group
  have hb'E : (k * c)⁻¹ * a * (k * c) ∈ E := hkc ▸ hbE
  have hb'K : (k * c)⁻¹ * a * (k * c) ∉ withKernel J := by
    rw [hkc]
    intro h
    apply hkK
    have := GrS4.map_conj_withKernel_le hcN (mem_map_of_mem (MulAut.conj c).toMonoidHom h)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rwa [show c * (c⁻¹ * (k⁻¹ * a * k) * c) * c⁻¹ = k⁻¹ * a * k by group] at this
  by_cases hiso : ∀ s ∈ S, s * s = 1 → (∀ e ∈ E, s * e = e * s) → s ∈ E
  ·
    have hEC : 2 ≤ Nat.card ↥(E ⊓ coreActionKernel J) := by
      have := Subgroup.card_le_of_le (zpowers_le.mpr (mem_inf.mpr ⟨haE, haK⟩) :
        zpowers a ≤ E ⊓ coreActionKernel J)
      rwa [Nat.card_zpowers, ha2] at this
    obtain ⟨⟨-, hbad, hEJ⟩, -⟩ := l34WCriterionDFact_of_certs G J S hJper hL34
      (GrS4.isSylowTwoIn_inf hS) hS2 hS.1 E hES hE (hE4 hkK) hEC
      fun s hs hss hsc => hiso s (mem_inf.mp hs).1 hss hsc
    refine hBad G a x J S A hset hcent hrun h3 W hW hWodd hWB hNJ K hKM hKc hsup hKN hSM hSyl
      (k * c) (hES hb'E) hb'K (fun hZ => ?_) ?_
    · have haJ : a ∈ J := hEJ hZ (mem_inf.mpr ⟨haE, mem_sup_right haK⟩)
      have hZJ : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
      have haZ : a ∈ zStarIn J := by
        rw [hZJ]
        exact mem_inf.mpr ⟨haJ, haK⟩
      exact mem_inf.mpr ⟨haS, haZ⟩
    · rcases hbad with ⟨⟨hZc, hZ4⟩, hU⟩ | ⟨hZ16, hF⟩
      · exact Or.inl ⟨hZc, hZ4, hU _ hb'E hb'K⟩
      · exact Or.inr ⟨hZ16, hF _ hb'E hb'K⟩
  · push Not at hiso
    obtain ⟨s₀, hs₀S, hs₀2, hs₀E, hs₀n⟩ := hiso
    exact exists_conj_of_not_isolated hset hcent hWB hSyl hES hE (fun e he => hE.1.1 e he _ hb'E)
      hs₀S hs₀2 hs₀E hs₀n (hs₀E _ hb'E)

end Fusion

section Bad

theorem l34Lemma43BadFusionStepKS_of_inputs (hMax : MaximalTwoComponentInput) :
    L34Lemma43BadFusionStepKS := by
  intro G _ _ a x J S A hset hcent _ h3 W hW hWodd hWB hNJ K hKM hKc hsup hKN _ hSyl g hgS
    _ haZ htype
  rcases htype with ⟨hZc, -, hU⟩ | ⟨h16, hF⟩
  · exact exists_conj_of_unitaryKS hMax hset hcent h3 hW hWodd hWB hNJ hKM hKc hsup hKN hSyl
      hgS hZc hU
  · have hZ : S ⊓ zStarIn J ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at h16
      norm_num at h16
    exact exists_conj_of_field hMax hset hcent h3 hWB hNJ hSyl hgS h16 hF (haZ hZ)

theorem l34Lemma43FusionStepKS_of_max (hMax : MaximalTwoComponentInput) :
    L34Lemma43FusionStepKS :=
  l34Lemma43FusionStepKS_of_bad (l34Lemma43BadFusionStepKS_of_inputs hMax)

end Bad

end CFSG.ComponentClassification.GrSLit.GrS5S
