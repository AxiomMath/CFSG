module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveR
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveL
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveQ

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerFivePumpBetaSevenInput : Prop :=
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
      Nonempty (↥M' ⧸ Open.fusionZStar ↥M' ≃* alternatingGroup (Fin 7))

theorem signalizerFivePumpThreeFixFourInput_of_betaSeven
    (hbal : Sol78.BalanceTwoComponentInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (h13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (h : SignalizerFivePumpBetaSevenInput) : SignalizerFivePumpThreeFixFourInput := by
  intro X _ _ _ hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv
    hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀ hj hP
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨haJc, ⟨θM, ρ, haM, hρ, h3⟩, E₀, hE₀, hE₀k, hE₀s⟩ := hP
  by_contra hMX
  have ht2 : t * t = 1 := by rw [← sq, ← hpair.1.1, pow_orderOf_eq_one]
  have hc2 : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  have ha2 : a * a = 1 := by rw [← sq, ← hao, pow_orderOf_eq_one]
  have htM : t ∈ normalizer (M : Set X) := mem_normalizer_iff_map_conj_eq.mpr hfix
  have hJcM' : Jc ≤ M := by
    have h1 := hJcM
    rwa [hfix, sup_idem] at h1
  have hJcMpc' : IsPComponent 2 (Jc.subgroupOf (M ⊓ centralizer ({t} : Set X))) := by
    have h1 := hJcMpc
    rwa [hfix, sup_idem] at h1
  have hJcCt : Jc ≤ centralizer ({t} : Set X) := (hJcJ.trans inf_le_left).trans hpair.1.2.1
  have hJcC : Jc ≤ centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X) :=
    le_inf hJcCt (hJcJ.trans inf_le_right)
  have hJcperf : ⁅Jc, Jc⁆ = Jc := UnbalancedCorr.commutator_eq_of_isPComponent hJcC hJcpc
  have hres := primeResidual_eq_top_of_isPComponent hJcC hJcpc
  have hβ : Fintype.card ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)) = 5 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hs4]
  let eJc : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃* alternatingGroup (Fin 5) :=
    χ.trans (Fintype.equivFinOfCardEq hβ).altCongrHom
  have hJcq : Nontrivial (↥Jc ⧸ pPrimeCore 2 ↥Jc) := by
    have : Nontrivial (alternatingGroup (Fin 5)) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; norm_num)
    exact eJc.toEquiv.nontrivial
  obtain ⟨τ, hτ5, hJcτ, hsurj, hO⟩ := exists_fix_of_pump hρ (by norm_num) (by norm_num) htM ht2
    hJcM' hJcCt hJcMpc' eJc hJcperf hJcK
  have hρt1 : ρ ⟨t, htM⟩ ≠ 1 := fun h1 =>
    false_of_mem_cak_of_not_cover hMC hMpc ht2 htc (hρ.mem_coreActionKernel htM h1) hJcM' hJcC
      hJcpc hcov
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
  obtain ⟨ρJ, hρJ⟩ := exists_isPermAction (M := J) (by norm_num) (by norm_num) θ
  obtain ⟨β, hβo, hβc, hβa, hβt, ⟨hβJ, hβ2, hβD⟩, hβM, hρβ⟩ := exists_beta_of_four hPump hN1 h13
    hML hSch hnab hKP hunb hnU hpair θ hρJ he₀ hc2 htc hcN hce hs4 hCtN hJcJ hres hinv hsubP χ hχ
    hMC hMpc hJcM' hJcperf hJcq hρ hτ5 hJcτ hsurj hO htM hJcCt hρt1 haJc ha2 hat haM h3 hE₀
    hE₀k hE₀s
  obtain ⟨M', hM'Y, hM'pc, hLM', hLM'pc, eM'⟩ := exists_seven_pump_of_beta hbal hPump hN1 hnab
    hKP hunb hnU hpair hc hao hac hMC hMpc hMX hρ (hJcM' haJc) haM h3 hβo hβc hβa hβM hρβ
  exact hMX (h X hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv
    hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀ hj
    ⟨haJc, ⟨θM, ρ, haM, hρ, h3⟩, ⟨E₀, hE₀, hE₀k, hE₀s⟩, β, M', hβo, hβc, hβa, hβt,
      ⟨hβJ, ρJ, hρJ, hβ2, hβD⟩, hρ.mem_coreActionKernel hβM hρβ, hM'Y, hM'pc, hLM', hLM'pc, eM'⟩)

end CFSG.ComponentClassification.SolMax
