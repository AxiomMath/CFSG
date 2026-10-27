module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveJ
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveF

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerFivePumpExactDataInput
    (P : ∀ (X : Type) [Group X], X → ∀ J : Subgroup X,
      (↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 9)) →
        X → ∀ e₀ : X, e₀ ∈ J → Subgroup X → Subgroup X → X → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (t : X) (J : Subgroup X), Sol78.IsSolomonPair t J 9 →
    ∀ (θ : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)) (c e₀ : X) (he₀ : e₀ ∈ J),
      orderOf c = 2 → t * c = c * t → c ∈ normalizer (J : Set X) →
      c * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J → (coreImage θ he₀).support.card = 4 →
    ∀ Jc : Subgroup X, Jc ≤ J ⊓ centralizer ({c} : Set X) →
      IsPComponent 2 (Jc.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X))) →
      (∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
        (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ → x ∈ Jc) →
      (∀ x ∈ Jc, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ) →
    ∀ χ : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃*
        alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)),
      (∀ (x : ↥Jc) (hx : (x : X) ∈ J),
        Perm.ofSubtype ((χ (x : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
          Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9))) = coreImage θ hx) →
    ∀ M : Subgroup X, M ≤ centralizer ({c} : Set X) →
      IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))) →
      Jc ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom →
      IsPComponent 2 (Jc.subgroupOf ((M ⊔ M.map (MulAut.conj t).toMonoidHom) ⊓
        centralizer ({t} : Set X))) →
      ¬ Jc ≤ UnbalancedLayer.coreActionKernel M →
      M.map (MulAut.conj t).toMonoidHom = M →
      ¬ Jc ⊔ (pPrimeCore 2 ↥M).map M.subtype = M →
    ∀ a : X, orderOf a = 2 → a * c = c * a → a * t = t * a → a ∈ normalizer (J : Set X) →
      (∃ (j₀ : X) (hj₀ : j₀ ∈ J), a * j₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J ∧
        (coreImage θ hj₀).support.card ≤ 4) →
      (∃ (j : X) (hjJ : j ∈ Jc), a * j⁻¹ ∈ UnbalancedLayer.coreActionKernel Jc ∧
        ((χ ((⟨j, hjJ⟩ : ↥Jc) : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
          Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9))).support.card ≤ 4) →
      P X t J θ c e₀ he₀ Jc M a →
      ⁅M, (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
          (centralizer ({a} : Set X)).subtype ⊓ centralizer ({c} : Set X)⁆ ≤
        (pPrimeCore 2 ↥(centralizer ({c} : Set X))).map (centralizer ({c} : Set X)).subtype

@[expose] def SignalizerFivePumpThreeFixMemInput : Prop :=
  SignalizerFivePumpExactDataInput fun X _ _ _ _ _ _ _ Jc M a =>
    a ∈ Jc ∧ ∃ (θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 7))
      (ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 7)) (haM : a ∈ normalizer (M : Set X)),
      IsPermAction θM ρ ∧ (ρ ⟨a, haM⟩).supportᶜ.card = 3

variable {X : Type} [Group X]

theorem signalizerFivePumpThreeFixInput_of_mem (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (h13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hmem : SignalizerFivePumpThreeFixMemInput) : SignalizerFivePumpThreeFixInput := by
  intro X _ _ _ hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv
    hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀ hj hP
  classical
  obtain ⟨r, θM, ρ, haM, hρ, hr79, h3⟩ := hP
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
  have hβ : Fintype.card ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)) = 5 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hs4]
  let eJc : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃* alternatingGroup (Fin 5) :=
    χ.trans (Fintype.equivFinOfCardEq hβ).altCongrHom
  obtain ⟨τ, hτ5, hJcτ, hsurj, hO⟩ := exists_fix_of_pump hρ (by omega) (by omega) htM ht2 hJcM'
    hJcCt hJcMpc' eJc hJcperf hJcK
  by_cases haJc : a ∈ Jc
  ·
    have hr7 : r = 7 := by
      obtain ⟨b, hb, hbe⟩ := hJcτ a haJc
      have hsupp : (ρ ⟨a, haM⟩).support ⊆ τ.supportᶜ := by
        have h1 : ρ ⟨a, haM⟩ = (b : Perm (Fin r)) := hbe.symm
        rw [h1]
        exact mem_fixAlt.mp hb
      have h1 := Finset.card_le_card hsupp
      rw [Finset.card_compl, Fintype.card_fin] at h1
      have h2 : (ρ ⟨a, haM⟩).supportᶜ.card = r - (ρ ⟨a, haM⟩).support.card := by
        rw [Finset.card_compl, Fintype.card_fin]
      have h4 : (ρ ⟨a, haM⟩).support.card ≤ r := by
        have := Finset.card_le_univ (ρ ⟨a, haM⟩).support
        rwa [Fintype.card_fin] at this
      omega
    subst hr7
    exact hmem X hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv
      hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀ hj
      ⟨haJc, θM, ρ, haM, hρ, h3⟩
  · obtain ⟨j₀, hj₀J, haj₀, hj₀4⟩ := hj₀
    obtain ⟨j', hj'Jc, haj', -⟩ := hj
    exact (false_of_three_fix_of_not_mem hPump hN1 h13 hML hSch hnab hKP hunb hnU hpair θ he₀
      hc2 hcN hce hs4 hJcJ χ hχ hMC hJcM' hρ (by omega) hτ5 hJcτ hsurj hO ha2 hac hat haM h3
      hj₀J haj₀ hj₀4 hj'Jc haj' haJc).elim

end CFSG.ComponentClassification.SolMax
