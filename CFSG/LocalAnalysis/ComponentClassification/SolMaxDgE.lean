module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDgD
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxDgC

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

@[expose] def SignalizerDiagInvertedInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (β c t a x' : X) (M' : Subgroup X),
    orderOf β = 2 → orderOf c = 2 → orderOf t = 2 → orderOf a = 2 →
    c * t = t * c → c * β = β * c → t * β = β * t →
    a * β = β * a → a * c = c * a → a * t = t * a →
    M' ≤ centralizer ({β} : Set X) →
    IsPComponent 2 (M'.subgroupOf (centralizer ({β} : Set X))) →
    M'.map (MulAut.conj c).toMonoidHom ≠ M' →
    M'.map (MulAut.conj t).toMonoidHom = M'.map (MulAut.conj c).toMonoidHom →
    ∀ (ψ : ↥M' ⧸ Open.fusionZStar ↥M' ≃* alternatingGroup (Fin 7))
      (ρ' : ↥(normalizer (M' : Set X)) →* Perm (Fin 7)), IsPermActionZ ψ ρ' →
    a ∈ M' ⊔ M'.map (MulAut.conj c).toMonoidHom →
    ∀ haN : a ∈ normalizer (M' : Set X), (ρ' ⟨a, haN⟩).supportᶜ.card = 3 →
    ∀ hON : (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map (centralizer ({a} : Set X)).subtype ⊓
        centralizer ({β} : Set X) ≤ normalizer (M' : Set X),
    (∀ (z : X) (hz : z ∈ (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
        (centralizer ({a} : Set X)).subtype ⊓ centralizer ({β} : Set X)), z * t = t * z →
      ρ' ⟨z, hON hz⟩ = 1) →
    ∀ hx' : x' ∈ (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
        (centralizer ({a} : Set X)).subtype ⊓ centralizer ({β} : Set X), x' * c = c * x' →
      ρ' ⟨x', hON hx'⟩ ≠ 1 → False

theorem signalizerFivePumpBetaDiagInput_of_diagInverted (hbal : Sol78.BalanceTwoComponentInput)
    (hPump : Sol78.AlternatingPumpUpInput) (h13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hDI : SignalizerDiagInvertedInput) : SignalizerFivePumpBetaDiagInput := by
  intro X _ _ _ hnab hKP hunb hnU t J hpair θ c e₀ he₀ hc htc hcN hce hs4 Jc hJcJ hJcpc hinv
    hsubP χ hχ M hMC hMpc hJcM hJcMpc hJcK hfix hcov a hao hac hat haJN hj₀ hj hP
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨haJc, ⟨θM, ρ, haM, hρ, h3⟩, -, β, M', hβo, hβc, hβa, hβt, ⟨hβJ, ρJ, hρJ, hβ2, hβD⟩,
    hβK, hM'Y, hM'pc, hLM', -, ⟨ψ⟩, hcM', htM'⟩ := hP
  by_contra hMX
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
  obtain ⟨hM'tc, hinv'⟩ := diag_facts_of_beta hPump hnab hKP hpair.1 hCtN hρJ he₀ hc htc hs4 hJcJ
    hJcpc hinv hsubP χ hχ hMC hMpc hJcM' htM θM hao haJc hβo hβc hβt hβJ hβ2 hβD hβK hM'Y hM'pc
    hLM' htM'
  obtain ⟨ρ', hρ'⟩ := exists_isPermActionZ (N := M') (by norm_num) (by norm_num) ψ
  have hβ2' : β * β = 1 := by rw [← sq, ← hβo, pow_orderOf_eq_one]
  have hMq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M _ hMC).mp hMpc).2.2
  have hMsub : (M.subgroupOf (centralizer ({c} : Set X))).IsSubnormal := hMpc.choose_spec.2.1
  have hE : zpowers β ≤ UnbalancedLayer.coreActionKernel M := zpowers_le.mpr hβK
  have hE2 : IsPGroup 2 (zpowers β) := isPGroup_zpowers_of_mul_self hβ2'
  have hβCc : β ∈ centralizer ({c} : Set X) := mem_centralizer_singleton_iff.mpr hβc
  have hEX : zpowers β ≤ centralizer ({c} : Set X) := zpowers_le.mpr hβCc
  have hCE : centralizer ((zpowers β : Subgroup X) : Set X) = centralizer ({β} : Set X) :=
    centralizer_zpowers_eq' β
  set L := GSLit.fixedLayer M (zpowers β) with hLdef
  have hLpc := GSLit.fixedLayer_isPComponent hMC hMsub hEX hE hE2 hMq
  rw [hCE, inf_comm] at hLpc
  have hle := GSLit.fixedLayer_le_inf M (zpowers β)
  rw [hCE] at hle
  have hLM : L ≤ M := hle.trans inf_le_left
  have hLY : L ≤ centralizer ({β} : Set X) ⊓ centralizer ({c} : Set X) := fun z hz =>
    mem_inf.2 ⟨(mem_inf.1 (hle hz)).2, hMC (hLM hz)⟩
  obtain ⟨hsup, hcoreL⟩ := GSLit.fixedLayer_sup_pPrimeCore hMq hE hE2
  obtain ⟨θL, hθL⟩ := exists_coreQuot_of_sup hLM hsup θM
  have hLperf : ⁅L, L⁆ = L := UnbalancedCorr.commutator_eq_of_isPComponent hLY hLpc
  have hLq : Nontrivial (↥L ⧸ pPrimeCore 2 ↥L) := nontrivial_coreQuot_of_seven θL
  have hcl := GSLit.fixedLayer_eq_closure hMq hE hE2
  have hcore : (pPrimeCore 2 ↥L).map L.subtype ≤ (pPrimeCore 2 ↥M).map M.subtype := by
    rw [hcoreL]
    exact inf_le_right
  have haL : a ∈ L := by
    rw [hLdef, hcl]
    refine subset_closure ⟨mem_inf.2 ⟨hJcM' haJc, ?_⟩, 1, by rw [pow_one]; exact hao⟩
    rw [hCE]
    exact mem_centralizer_singleton_iff.mpr hβa.symm
  have hcβ : c ∈ centralizer ({β} : Set X) := mem_centralizer_singleton_iff.mpr hβc.symm
  obtain ⟨hM'cY, hM'cpc⟩ := isPComponent_conj hM'Y hM'pc hcβ
  obtain ⟨hDN, -, -, -⟩ := GSThmB.B5a.pComponent_sup_facts hM'Y hM'cY hM'pc hM'cpc
  have hLN : L ≤ normalizer (M' : Set X) := hLM'.trans hDN
  have hneL := exists_ne_one_of_diag hcβ hM'Y hM'pc hρ' hLM' (hLM.trans hMC) hLperf hLq hLN
  have hresL := primeResidual_eq_top_of_isPComponent hLY hLpc
  obtain ⟨hsurjL, hAL, hOL⟩ := image_of_seven hLN hLperf hresL θL hneL
  have hcard := card_support_eq_of_two_actions hρ hLM θL (fun x hxL _ => hθL ⟨x, hxL⟩) hLN
    hsurjL hAL hOL haL
  have ha3 : (ρ' ⟨a, hLN haL⟩).supportᶜ.card = 3 := by
    have h1 : (ρ ⟨a, haM⟩).supportᶜ.card = 7 - (ρ ⟨a, haM⟩).support.card := by
      rw [Finset.card_compl, Fintype.card_fin]
    have h2 : (ρ ⟨a, haM⟩).support.card ≤ 7 := by
      have := Finset.card_le_univ (ρ ⟨a, haM⟩).support
      rwa [Fintype.card_fin] at this
    have h4 : (ρ' ⟨a, hLN haL⟩).support.card = (ρ ⟨a, haM⟩).support.card := hcard
    rw [Finset.card_compl, Fintype.card_fin, h4]
    omega
  have hON := inf_le_normalizer_of_balance hbal hao hβo hβa.symm hM'Y hM'pc
  have hinvR : ∀ (z : X) (hz : z ∈ (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
      (centralizer ({a} : Set X)).subtype ⊓ centralizer ({β} : Set X)), z * t = t * z →
      ρ' ⟨z, hON hz⟩ = 1 := fun z hz hzt =>
    hinv' ψ ρ' hρ' z (mem_inf.1 hz).1 (mem_centralizer_singleton_iff.mp (mem_inf.1 hz).2) hzt
      (hON hz)
  set Oa := (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
    (centralizer ({a} : Set X)).subtype with hOadef
  have hOaodd : Odd (Nat.card Oa) := by
    rw [hOadef, card_map_of_injective (centralizer ({a} : Set X)).subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hX₀N : Oa ⊓ centralizer ({c} : Set X) ≤ normalizer (M : Set X) :=
    inf_le_normalizer_of_balance hbal hao hc hac hMC hMpc
  have hX₀K : ¬ Oa ⊓ centralizer ({c} : Set X) ≤ UnbalancedLayer.coreActionKernel M := fun h =>
    hMX ((commutator_le_of_le_coreActionKernel h).trans (pPrimeCore_le_of_isPComponent hMC hMpc))
  obtain ⟨x, hxX₀, hxK⟩ : ∃ x ∈ Oa ⊓ centralizer ({c} : Set X),
      x ∉ UnbalancedLayer.coreActionKernel M := by
    by_contra h
    push Not at h
    exact hX₀K h
  have hx1 : ρ ⟨x, hX₀N hxX₀⟩ ≠ 1 := fun h => hxK (hρ.mem_coreActionKernel _ h)
  have hX₀odd : Odd (Nat.card ↥(Oa ⊓ centralizer ({c} : Set X))) :=
    hOaodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hβCa : β ∈ centralizer ({a} : Set X) := mem_centralizer_singleton_iff.mpr hβa
  have hβX₀ : zpowers β ≤ normalizer ((Oa ⊓ centralizer ({c} : Set X) : Subgroup X) : Set X) :=
    zpowers_le.mpr (inf_mem_normalizer' (le_normalizer_pPrimeCore (le_normalizer hβCa))
      (le_normalizer hβCc))
  have hβM : β ∈ normalizer (M : Set X) := hβK.1
  have hβN : zpowers β ≤ normalizer (M : Set X) := zpowers_le.mpr hβM
  have hρβ : ρ ⟨β, hβM⟩ = 1 := hρ.eq_one_of_mem_coreActionKernel (by norm_num) hβK
  have hA1 : ∀ (g : X) (hg : g ∈ zpowers β), ρ ⟨g, hβN hg⟩ = 1 := by
    intro g hg
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    have h1 : (⟨β ^ k, hβN hg⟩ : ↥(normalizer (M : Set X))) = ⟨β, hβM⟩ ^ k := rfl
    rw [h1, map_zpow, hρβ, one_zpow]
  obtain ⟨x', hx'X₀, hx'β, hx'1⟩ := exists_centralizing_of_ne_one hX₀N hX₀odd
    (isPGroup_zpowers_of_mul_self hβ2') hβX₀ hβN hA1 hxX₀ hx1
  have hx'β' : x' * β = β * x' := (mem_centralizer_iff.mp hx'β β (mem_zpowers β)).symm
  have hx'Oa : x' ∈ Oa := (mem_inf.mp hx'X₀).1
  have hx'Cc : x' ∈ centralizer ({c} : Set X) := (mem_inf.mp hx'X₀).2
  have hx'm : x' ∈ Oa ⊓ centralizer ({β} : Set X) :=
    mem_inf.2 ⟨hx'Oa, mem_centralizer_singleton_iff.mpr hx'β'⟩
  have hx'1' : ρ' ⟨x', hON hx'm⟩ ≠ 1 := by
    intro h1
    have hx'L : x' ∈ normalizer (L : Set X) :=
      mem_normalizer_fixedLayer hMq hE hE2 (hX₀N hx'X₀) hx'β'
    have h2 := mem_coreActionKernel_of_eq_one_of_image hLN θL hsurjL hAL hOL (hON hx'm) hx'L h1
    have h3 := mem_coreActionKernel_of_fixedLayer hMC hMpc hLM hLperf hLq hsup hcore hx'Cc h2
    exact hx'1 (hρ.eq_one_of_mem_coreActionKernel (by norm_num) h3)
  exact hDI X β c t a x' M' hβo hc hpair.1.1 hao htc.symm hβc.symm hβt.symm hβa.symm hac hat
    hM'Y hM'pc hcM' hM'tc ψ ρ' hρ' (hLM' haL) (hLN haL) ha3 hON hinvR hx'm
    (mem_centralizer_singleton_iff.mp hx'Cc) hx'1'

theorem signalizerFivePumpBetaInvInput_of_diagInverted (hbal : Sol78.BalanceTwoComponentInput)
    (hPump : Sol78.AlternatingPumpUpInput) (h13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    (hDI : SignalizerDiagInvertedInput) : SignalizerFivePumpBetaInvInput :=
  signalizerFivePumpBetaInvInput_of_betaDiag
    (signalizerFivePumpBetaDiagInput_of_diagInverted hbal hPump h13 hML hSch hDI)

end CFSG.ComponentClassification.SolMax
