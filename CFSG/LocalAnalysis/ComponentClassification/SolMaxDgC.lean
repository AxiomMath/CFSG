module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDgB
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveW

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerFivePumpBetaInvInput : Prop :=
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
      M'.map (MulAut.conj c).toMonoidHom ≠ M' ∧ M'.map (MulAut.conj t).toMonoidHom ≠ M' ∧
      (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map (centralizer ({a} : Set X)).subtype ⊓
          centralizer ({c} : Set X) ⊓ centralizer ({β} : Set X) ⊓ centralizer ({t} : Set X) ≤
        UnbalancedLayer.coreActionKernel M

theorem signalizerFivePumpBetaInvInput_of_betaDiag (h : SignalizerFivePumpBetaDiagInput) :
    SignalizerFivePumpBetaInvInput :=
  signalizerFivePumpExactDataInput_mono
    (fun _ _ _ _ _ _ _ _ _ _ _ ⟨ha, hM, hE, β, M', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, _⟩ => ⟨ha, hM, hE, β, M', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩) h

theorem signalizerFivePumpBetaDiagInput_of_betaInv (hbal : Sol78.BalanceTwoComponentInput)
    (hPump : Sol78.AlternatingPumpUpInput) (h13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (h : SignalizerFivePumpBetaInvInput) : SignalizerFivePumpBetaDiagInput := by
  intro X _ _ _ hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv
    hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀ hj hP
  obtain ⟨haJc, hθM, hE, β, M', hβo, hβc, hβa, hβt, ⟨hβJ, ρJ, hρJ, hβ2, hβD⟩, hβK, hM'Y, hM'pc,
    hLM', hLM'pc, eM', hcM', htM'⟩ := hP
  by_cases hle : (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
      (centralizer ({a} : Set X)).subtype ⊓ centralizer ({c} : Set X) ⊓
        centralizer ({β} : Set X) ⊓ centralizer ({t} : Set X) ≤
      UnbalancedLayer.coreActionKernel M
  · exact h X hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv
      hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀ hj
      ⟨haJc, hθM, hE, β, M', hβo, hβc, hβa, hβt, ⟨hβJ, ρJ, hρJ, hβ2, hβD⟩, hβK, hM'Y, hM'pc,
        hLM', hLM'pc, eM', hcM', htM', hle⟩
  exfalso
  classical
  obtain ⟨θM, ρ, haM, hρ, -⟩ := hθM
  have htM : t ∈ normalizer (M : Set X) := mem_normalizer_iff_map_conj_eq.mpr hfix
  have hJcM' : Jc ≤ M := by
    have h1 := hJcM
    rwa [hfix, sup_idem] at h1
  have hCtN : centralizer ({t} : Set X) ≤ normalizer (J : Set X) := by
    have hCt : centralizer ((zpowers t : Subgroup X) : Set X) = centralizer ({t} : Set X) :=
      UnbalancedLayer.centralizer_zpowers_eq t
    have ht := hpair.1.1
    have hT1 : zpowers t ≠ ⊥ := by
      intro h1
      rw [zpowers_eq_bot] at h1
      rw [h1, orderOf_one] at ht
      exact absurd ht (by decide)
    have hT2 : IsPGroup 2 (zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
    have hJT : FooteLit.IsTwoComponentIn J (centralizer ((zpowers t : Subgroup X) : Set X)) := by
      rw [hCt]
      exact ⟨hpair.1.2.1, hpair.1.2.2.1⟩
    have hN := Sol78H.normalizer_le_normalizer_of_isTwoComponentIn_centralizer_alt h13 hML hSch
      hnab hKP hunb hnU hpair.2.1 hpair.2.2.1 ⟨t, J, hpair.1⟩ hpair.2.2.2.1 hT1 hT2 hJT
      hpair.1.2.2.2
    intro g hg
    apply hN
    rw [← hCt] at hg
    exact Subgroup.centralizer_le_normalizer _ hg
  obtain ⟨z, hz, hzK⟩ : ∃ z ∈ (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
      (centralizer ({a} : Set X)).subtype ⊓ centralizer ({c} : Set X) ⊓
        centralizer ({β} : Set X) ⊓ centralizer ({t} : Set X),
      z ∉ UnbalancedLayer.coreActionKernel M := by
    by_contra hall
    push Not at hall
    exact hle hall
  obtain ⟨⟨⟨hzO, hzc⟩, hzβ⟩, hzt⟩ := hz
  have hzM : z ∈ normalizer (M : Set X) :=
    inf_le_normalizer_of_balance hbal hao hc hac hMC hMpc (mem_inf.2 ⟨hzO, hzc⟩)
  have hz1 : ρ ⟨z, hzM⟩ ≠ 1 := fun h1 => hzK (hρ.mem_coreActionKernel hzM h1)
  exact false_of_diag_of_centralized hbal hPump hnab hKP hpair.1 hCtN hρJ he₀ hc htc hs4 hJcJ
    hJcpc hinv hsubP χ hχ hMC hMpc hJcM' htM θM hρ hao haJc hβo hβc hβa hβt hβJ hβ2 hβD hβK hM'Y
    hM'pc hLM' eM' htM' hzO (mem_centralizer_singleton_iff.mp hzc)
    (mem_centralizer_singleton_iff.mp hzβ) (mem_centralizer_singleton_iff.mp hzt) hzM hz1

end CFSG.ComponentClassification.SolMax
