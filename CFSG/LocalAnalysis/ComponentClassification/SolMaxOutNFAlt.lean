module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutNFAltI
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutNFAltII

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerCaseOneConjugateOutsideAltInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (t : X) (J : Subgroup X) (n : ℕ)
    (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X) (D : Finset (Fin n)),
    Sig36 X t J n e E D → 11 ≤ n → Sol78.signalizerCompletion E E ≠ ⊥ →
    ∀ M : Subgroup X, M ≤ normalizer (Sol78.signalizerCompletion E E : Set X) →
      IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))) →
      J ≤ M →
      ∀ hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X),
      J ⊔ FooteLit.oddCoreIn M = M →
    ∀ (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)), IsPermAction θ ρ →
    ∀ Q : Subgroup X,
      Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M → IsPGroup 2 Q →
      Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
        UnbalancedLayer.coreActionKernel M)).factorization 2 → t ∈ Q →
      (∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
        centralizer ({x} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
      (∀ T : Subgroup X, T ≤ Q → T ≠ ⊥ →
        normalizer (T : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) →
    ∀ (a g : X), a ∈ Q → g ∉ normalizer (Sol78.signalizerCompletion E E : Set X) →
      ∀ hs : g⁻¹ * a * g ∈ normalizer (Sol78.signalizerCompletion E E : Set X),
      g⁻¹ * a * g ∈ normalizer (Q : Set X) →
      ρ ⟨g⁻¹ * a * g, hHN hs⟩ * ρ ⟨g⁻¹ * a * g, hHN hs⟩ = 1 → ρ ⟨g⁻¹ * a * g, hHN hs⟩ ≠ 1 →
    ∀ (x : X) (hx : x ∈ M), x ∈ oddGen (centralizer ({g⁻¹ * a * g} : Set X)) → x * x = 1 →
      (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      FourForm (ρ ⟨g⁻¹ * a * g, hHN hs⟩) (ρ ⟨x, le_normalizer hx⟩) →
    ∀ hx' : g * x * g⁻¹ ∈ normalizer (Sol78.signalizerCompletion E E : Set X),
      g * x * g⁻¹ ∉ M → g⁻¹ * a * g * (g⁻¹ * a * g) = 1 →
      n - (ρ ⟨g * x * g⁻¹, hHN hx'⟩).support.card < 5 →
    ∀ (y : X) (hy : y ∈ M), y * y = 1 → y * (g * x * g⁻¹) = g * x * g⁻¹ * y →
      ρ ⟨y, le_normalizer hy⟩ = ρ ⟨g * x * g⁻¹, hHN hx'⟩ →
      y ∈ oddGen (centralizer ({g * x * g⁻¹} : Set X) ⊓ centralizer ({a} : Set X)) →
      y * (g * x * g⁻¹) ∈ oddGen (centralizer ({a} : Set X) ⊓
        (normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
          UnbalancedLayer.coreActionKernel M)) →
      centralizer ({y * (g * x * g⁻¹)} : Set X) ≤
        normalizer (Sol78.signalizerCompletion E E : Set X) →
      ((∃ (T : Subgroup X) (r : ℕ), 5 ≤ r ∧
        T ≤ centralizer ({a} : Set X) ⊓ (normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
          UnbalancedLayer.coreActionKernel M) ∧
        ∃ f : ↥T →* alternatingGroup (Fin r), Function.Surjective f) ∨
      (n = 11 ∧ ((ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card = 4 ∨
        (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card = 8))) → False

theorem signalizerCaseOneConjugateOutsideKernelFormInput_of_alt
    (hAlt : SignalizerCaseOneConjugateOutsideAltInput) :
    SignalizerCaseOneConjugateOutsideKernelFormInput := by
  intro X _ _ _ t J n e E D S hn hW M hMH hMpc hJM hHN hsup θ ρ hρ Q hQK hQ2 hQcard htQ hA hNT a g
    ha hgH hs hsNQ hσ2 hσ1 x hxM hxo hx2 hx4 hxf hx' hx'M hs2 h5 y hyM hy2 hyx' hρy hyo hko hCk
  refine hAlt X t J n e E D S hn hW M hMH hMpc hJM hHN hsup θ ρ hρ Q hQK hQ2 hQcard htQ hA hNT a g
    ha hgH hs hsNQ hσ2 hσ1 x hxM hxo hx2 hx4 hxf hx' hx'M hs2 h5 y hyM hy2 hyx' hρy hyo hko hCk ?_
  have hodd : Odd n := S.pair.2.1
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hσ1
    have h1 : (⟨g⁻¹ * 1 * g, hHN hs⟩ : ↥(normalizer (M : Set X))) = 1 :=
      Subtype.ext (show g⁻¹ * 1 * g = 1 by group)
    rw [h1, map_one]
  have hσ2' : ρ ⟨g⁻¹ * a * g, hHN hs⟩ ^ 2 = 1 := by rw [sq]; exact hσ2
  obtain ⟨q, hq⟩ := Perm.two_dvd_card_support hσ2'
  have hσc : (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card ≤ n := by
    have := Finset.card_le_univ (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support
    rwa [Fintype.card_fin] at this
  obtain ⟨k, hk⟩ := hodd
  by_cases h11 : n = 11 ∧ ((ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card = 4 ∨
      (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card = 8)
  · exact Or.inr h11
  · left
    by_cases h5s : 5 ≤ n - (ρ ⟨g⁻¹ * a * g, hHN hs⟩).support.card
    · exact S.exists_alt_of_five_fix hn hMH hMpc hHN hρ hQK hQ2 hA hNT ha ha1 hs hs2 hxM hxo hx2
        hx4 hxf hx' h5 h5s (fun h6 => by omega)
    · exact exists_alt_of_four_fix hn hMH hMpc hHN hρ hQK hQ2 hNT ha ha1 hs hs2 hxM hxo hx2 hxf
        hx'M (by omega)

theorem signalizerCaseOneConjugateFormInput_of_alt (hD2 : SignalizerConjKernelExclusion)
    (hAlt : SignalizerCaseOneConjugateOutsideAltInput) : SignalizerCaseOneConjugateFormInput :=
  signalizerCaseOneConjugateFormInput_of_kernelForm hD2
    (signalizerCaseOneConjugateOutsideKernelFormInput_of_alt hAlt)

theorem signalizerTrivialityInput_of_residues_alt
    (hmax : SolAltLit.MaximalAltComponentInput) (hbal : Sol78.BalanceTwoComponentInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hsmall : SignalizerSmallDegreeInput) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hSwap : SignalizerSwapAltExclusion)
    (hGT : Sol78.StronglyClosedResidualInput) (hA : SignalizerClaimASmallInput)
    (h2 : SignalizerCaseTwoFinishInput) (hAlt : SignalizerCaseOneConjugateOutsideAltInput)
    (hR11 : SignalizerCaseOneStrongClosureElevenInput) (h9 : SignalizerNineInput) :
    SolAltLit.SignalizerTrivialityInput :=
  signalizerTrivialityInput_of_residues_conjugateForm hmax hbal hPump hN1 hsmall hT13 hML hSch
    hSwap hGT hA h2
    (signalizerCaseOneConjugateFormInput_of_alt
      (signalizerConjKernelExclusion_of_inputs
        (balanceLemmaInput_of_smallDegree hbal hPump hN1 hsmall)
        (signalizerLemma35_of_smallDegree hbal hPump hN1 hsmall) hT13 hML hSch) hAlt)
    hR11 h9

end CFSG.ComponentClassification.SolMax
