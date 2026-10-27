module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveS
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveV

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerFivePumpBetaDiagInput : Prop :=
  SignalizerFivePumpExactDataInput fun X _ t J θ c _ he₀ Jc M a =>
    a ∈ Jc ∧ (∃ (θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 7))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 7)) (haM : a ∈ normalizer (M : Set X)),
      IsPermAction θM ρ ∧ (ρ ⟨a, haM⟩).supportᶜ.card = 3) ∧
    (∃ E₀ : Subgroup X, E₀ ≤ J ⊓ centralizer ({c} : Set X) ⊓ centralizer ({a} : Set X) ∧
      Nonempty (E₀ ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
      ∀ (x : X) (hx : x ∈ J), x ∈ E₀ → (coreImage θ hx).support ⊆ (coreImage θ he₀).support) ∧
    ∃ (β : X) (M' : Subgroup X), orderOf β = 2 ∧ β * c = c * β ∧ β * a = a * β ∧
      β * t = t * β ∧
      (∃ (hβJ : β ∈ normalizer (J : Set X)) (ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin 9)),
        IsPermAction θ ρJ ∧ (ρJ ⟨β, hβJ⟩).support.card = 2 ∧
        (ρJ ⟨β, hβJ⟩).support ⊆ (coreImage θ he₀).support) ∧
      β ∈ UnbalancedLayer.coreActionKernel M ∧ M' ≤ centralizer ({β} : Set X) ∧
      IsPComponent 2 (M'.subgroupOf (centralizer ({β} : Set X))) ∧
      GSLit.fixedLayer M (zpowers β) ≤ M' ⊔ M'.map (MulAut.conj c).toMonoidHom ∧
      IsPComponent 2 ((GSLit.fixedLayer M (zpowers β)).subgroupOf
        ((M' ⊔ M'.map (MulAut.conj c).toMonoidHom) ⊓ centralizer ({c} : Set X))) ∧
      Nonempty (↥M' ⧸ Open.fusionZStar ↥M' ≃* alternatingGroup (Fin 7)) ∧
      M'.map (MulAut.conj c).toMonoidHom ≠ M' ∧ M'.map (MulAut.conj t).toMonoidHom ≠ M'

theorem signalizerFivePumpBetaSevenInput_of_betaDiag (hPump : Sol78.AlternatingPumpUpInput)
    (h : SignalizerFivePumpBetaDiagInput) : SignalizerFivePumpBetaSevenInput := by
  intro X _ _ _ hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv
    hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀ hj hP
  obtain ⟨haJc, hθM, hE, β, M', hβo, hβc, hβa, hβt, ⟨hβJ, ρJ, hρJ, hβ2, hβD⟩, hβK, hM'Y, hM'pc,
    hLM', hLM'pc, eM'⟩ := hP
  by_cases hcase : M'.map (MulAut.conj c).toMonoidHom = M' ∨
      M'.map (MulAut.conj t).toMonoidHom = M'
  · exfalso
    obtain ⟨θM, -, -, -, -⟩ := hθM
    have htM : t ∈ normalizer (M : Set X) := mem_normalizer_iff_map_conj_eq.mpr hfix
    have hJcM' : Jc ≤ M := by
      have h1 := hJcM
      rwa [hfix, sup_idem] at h1
    exact false_of_seven_pump_of_normalizes hPump hnab hKP hpair.1 hρJ he₀ hc htc hcN hce hs4
      hJcJ hJcpc hinv hsubP χ hχ hMC hMpc hJcM' htM θM hβo hβc hβt hβJ hβ2 hβD hβK hM'Y hM'pc
      hLM' eM' hcase
  · push Not at hcase
    exact h X hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv
      hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀ hj
      ⟨haJc, hθM, hE, β, M', hβo, hβc, hβa, hβt, ⟨hβJ, ρJ, hρJ, hβ2, hβD⟩, hβK, hM'Y, hM'pc,
        hLM', hLM'pc, eM', hcase.1, hcase.2⟩

end CFSG.ComponentClassification.SolMax
