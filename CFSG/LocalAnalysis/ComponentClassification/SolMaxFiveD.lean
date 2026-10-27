module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveC
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36X
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerFivePumpExactInput : Prop :=
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
      ⁅M, (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
          (centralizer ({a} : Set X)).subtype ⊓ centralizer ({c} : Set X)⁆ ≤
        (pPrimeCore 2 ↥(centralizer ({c} : Set X))).map (centralizer ({c} : Set X)).subtype

theorem signalizerFivePumpBalanceInput_of_exact (hbal : Sol78.BalanceTwoComponentInput)
    (hE : SignalizerFivePumpExactInput) : SignalizerFivePumpBalanceInput := by
  intro X _ _ _ hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv
    hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK a hao hac hat haJN hj₀ hj
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc2 : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc
    omega
  have ha2 : a * a = 1 := by rw [← sq, ← hao, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hao
    omega
  have ht2 : orderOf t = 2 := hpair.1.1
  have htcC : t ∈ centralizer ({c} : Set X) := mem_centralizer_singleton_iff.mpr htc
  set Cc : Subgroup X := centralizer ({c} : Set X) with hCcdef
  set Ca : Subgroup X := centralizer ({a} : Set X) with hCadef
  set Oc := (pPrimeCore 2 ↥Cc).map Cc.subtype with hOcdef
  set Oa := (pPrimeCore 2 ↥Ca).map Ca.subtype with hOadef
  have hβ : Fintype.card ↥((coreImage θ he₀).supportᶜ : Finset (Fin 9)) = 5 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    omega
  let eJc : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃* alternatingGroup (Fin 5) :=
    χ.trans (Fintype.equivFinOfCardEq hβ).altCongrHom
  have hJcCt : Jc ≤ centralizer ({t} : Set X) := (hJcJ.trans inf_le_left).trans hpair.1.2.1
  have hJcC : Jc ≤ centralizer ({t} : Set X) ⊓ Cc := le_inf hJcCt (hJcJ.trans inf_le_right)
  have hJcperf : ⁅Jc, Jc⁆ = Jc := UnbalancedCorr.commutator_eq_of_isPComponent hJcC hJcpc
  have hres := primeResidual_eq_top_of_isPComponent hJcC hJcpc
  have hMperf : ⁅M, M⁆ = M := UnbalancedCorr.commutator_eq_of_isPComponent hMC hMpc
  obtain ⟨hMtC, hMtpc⟩ := isPComponent_conj hMC hMpc htcC
  have hMtN : M.map (MulAut.conj t).toMonoidHom ≤ normalizer (M : Set X) := by
    by_cases hfix : M.map (MulAut.conj t).toMonoidHom = M
    · rw [hfix]
      exact le_normalizer
    · exact fun z hz => (GSThmB.B5a.le_coreActionKernel_of_ne hMC hMtC hMpc hMtpc
        (Ne.symm hfix) hz).1
  have hJcN : Jc ≤ normalizer (M : Set X) := hJcM.trans (sup_le le_normalizer hMtN)
  by_contra hMX
  have hS : zpowers a ≠ ⊥ := fun h => ha1 (zpowers_eq_bot.mp h)
  have hT : zpowers c ≠ ⊥ := fun h => hc1 (zpowers_eq_bot.mp h)
  have hST : zpowers a ≤ centralizer ((zpowers c : Subgroup X) : Set X) := by
    rw [centralizer_zpowers_eq', zpowers_le, mem_centralizer_singleton_iff]
    exact hac
  obtain ⟨-, hbc, -⟩ := hbal X (zpowers a) (zpowers c) hS hT
    (IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [sq]; exact ha2))
    (IsElementaryAbelian.zpowers_of_pow_eq_one (by rw [sq]; exact hc2)) hST
  have hCc' : centralizer ((zpowers c : Subgroup X) : Set X) = Cc := centralizer_zpowers_eq' c
  have hCa' : centralizer ((zpowers a : Subgroup X) : Set X) = Ca := centralizer_zpowers_eq' a
  rw [hCc', hCa'] at hbc
  obtain ⟨hXN, hcc⟩ := hbc M ⟨hMC, hMpc⟩
  obtain ⟨haN', -, hOM⟩ := hcc hMX
  have haM : a ∈ normalizer (M : Set X) := by
    obtain ⟨⟨g, hg⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp haN'
    obtain ⟨hga, hgN⟩ := mem_inf.mp hg
    rcases eq_one_or_eq_of_mem_zpowers ha2 hga with h | h
    · exact absurd (Subtype.ext h) hg1
    · exact h ▸ hgN
  have hOMC : (pPrimeCore 2 ↥M).map M.subtype ≤ Oc := pPrimeCore_le_of_isPComponent hMC hMpc
  have haK : a ∉ UnbalancedLayer.coreActionKernel M := by
    intro haK
    have h1 : ⁅M, zpowers a ⊓ normalizer (M : Set X)⁆ ≤ Oc :=
      (commutator_le_of_le_coreActionKernel (inf_le_left.trans (zpowers_le.mpr haK))).trans
        hOMC
    have h2 : Oc ⊔ M ≤ Oc := by
      have h3 : GH74.GLS.pPrimeCoreOf 2 Cc ⊔ M = GH74.GLS.pPrimeCoreOf 2 Cc ⊔
          ⁅M, zpowers a ⊓ normalizer (M : Set X)⁆ := hOM
      change GH74.GLS.pPrimeCoreOf 2 Cc ⊔ M ≤ GH74.GLS.pPrimeCoreOf 2 Cc
      rw [h3]
      exact sup_le le_rfl h1
    exact not_le_pPrimeCore_of_isPComponent hMC hMpc (le_sup_right.trans h2)
  have hXNM : Oa ⊓ Cc ≤ normalizer (M : Set X) :=
    le_normalizer_of_le_normalizer_sup hMC hMpc inf_le_right hXN
  have hX : ¬ Oa ⊓ Cc ≤ UnbalancedLayer.coreActionKernel M := fun h =>
    hMX ((commutator_le_of_le_coreActionKernel h).trans hOMC)
  have hXodd : Odd (Nat.card ↥(Oa ⊓ Cc)) := by
    have h1 : Odd (Nat.card Oa) := by
      rw [hOadef, card_map_of_injective Ca.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact h1.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hXa : Oa ⊓ Cc ≤ Ca := inf_le_left.trans (map_subtype_le _)
  obtain ⟨j, hjJc, haj, hjs⟩ := hj
  have hfive : Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin 5)) → False := by
    rintro ⟨ψ⟩
    exact hX (le_coreActionKernel_of_five hMperf ψ hJcN hJcperf hres eJc hJcK haM ha2 haK hjJc
      haj hXNM hXa hXodd)
  by_cases hfix : M.map (MulAut.conj t).toMonoidHom = M
  · have hJcM' : Jc ≤ M := by
      have h1 := hJcM
      rwa [hfix, sup_idem] at h1
    by_cases hcov : Jc ⊔ (pPrimeCore 2 ↥M).map M.subtype = M
    · obtain ⟨θM, -⟩ := exists_coreQuot_of_sup' hJcM' hcov eJc
      exact hfive ⟨(QuotientGroup.quotientMulEquivOfEq
        (fusionZStar_eq_of_alt (by norm_num) θM)).trans θM⟩
    · exact hMX (hE X hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc
        hinv hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀
        ⟨j, hjJc, haj, hjs⟩)
  · obtain ⟨φ⟩ := swap_type_in htcC ht2 hMC hMpc hfix hJcM hJcCt hJcMpc
    have hZ := fusionZStar_eq_of_alt (by norm_num) eJc
    exact hfive ⟨φ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans eJc)⟩

end CFSG.ComponentClassification.SolMax
