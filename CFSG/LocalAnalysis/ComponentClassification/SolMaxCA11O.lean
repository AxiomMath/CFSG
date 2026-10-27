module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11K
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxCA11N

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerCaseOneConjugateOutsideAltRInput : Prop :=
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
      (∃ (T : Subgroup X) (r : ℕ), 5 ≤ r ∧
        T ≤ centralizer ({a} : Set X) ⊓ (normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
          UnbalancedLayer.coreActionKernel M) ∧
        ∃ f : ↥T →* alternatingGroup (Fin r), Function.Surjective f) → False

theorem signalizerCaseOneConjugateOutsideAltEightInput_of_altR
    (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion)
    (hAltR : SignalizerCaseOneConjugateOutsideAltRInput) :
    SignalizerCaseOneConjugateOutsideAltEightInput := by
  intro X _ _ _ t J n e E D S hn hW M hMH hMpc hJM hHN hsup θ ρ hρ Q hQK hQ2 hQcard htQ hA hNT a g
    ha hgH hs hsNQ hσ2 hσ1 x hxM hxo hx2 hx4 hxf hx' hx'M hs2 h5 y hyM hy2 hyx' hρy hyo hko hCk h
  rcases h with h | ⟨h11, h8⟩
  · exact hAltR X t J n e E D S hn hW M hMH hMpc hJM hHN hsup θ ρ hρ Q hQK hQ2 hQcard htQ hA hNT
      a g ha hgH hs hsNQ hσ2 hσ1 x hxM hxo hx2 hx4 hxf hx' hx'M hs2 h5 y hyM hy2 hyx' hρy hyo hko
      hCk h
  · subst h11
    exact S.false_of_conj_eight_eleven h33 h35 hT13 hML hSch hPump hN1 hMH hMpc hJM hHN hsup hρ
      hA hs hs2 h8 hxM hxo hx2 hx4 hxf hy2 hyx' hyo hko hCk

end CFSG.ComponentClassification.SolMax
