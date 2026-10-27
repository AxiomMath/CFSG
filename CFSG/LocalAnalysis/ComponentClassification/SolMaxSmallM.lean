module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallL
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallD
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallG
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallH
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallI

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

namespace Sol33

variable {X : Type} [Group X] [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {y : X} (S : Sol33 X t J n θ E D y)
include S

theorem exists_balanced_pump_seven
    (hbal : Sol78.BalanceTwoComponentInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) (hHe : SignalizerHeldPumpExclusionInput) (hn : n = 11)
    {c e₀ : X} (hcB : c ∈ centralizer ((E ⊔ zpowers y : Subgroup X) : Set X))
    (htc : t * c = c * t) (hcN : c ∈ normalizer (J : Set X)) (hc : orderOf c = 2)
    (he₀ : e₀ ∈ J) (hce : c * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J)
    (hs4 : (coreImage θ he₀).support.card = 4)
    (hτc : ∀ (e : X) (he : e ∈ E), coreImage θ (S.le he) * coreImage θ he₀ =
      coreImage θ he₀ * coreImage θ (S.le he))
    (hdich : (∀ (e : X) (he : e ∈ E),
        (coreImage θ (S.le he)).support ⊆ (coreImage θ he₀).support) ∨
      (∀ (e : X) (he : e ∈ E),
        (coreImage θ (S.le he)).support ⊆ (coreImage θ he₀).supportᶜ)) :
    ∃ Jc M : Subgroup X, Jc ≤ J ⊓ centralizer ({c} : Set X) ∧
      (∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
        (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ → x ∈ Jc) ∧
      M ≤ centralizer ({c} : Set X) ∧ IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X))) ∧
      Jc ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom ∧
      ¬ Jc ≤ UnbalancedLayer.coreActionKernel M ∧
      (∀ (g : X) (hgN : g ∈ normalizer (J : Set X)), g * c = c * g →
        (∀ (x : X) (hx : x ∈ J), (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ →
          (coreImage θ ((mem_normalizer_iff.mp hgN x).mp hx)).support ⊆
            (coreImage θ he₀).supportᶜ) →
        g ∈ normalizer (Jc : Set X)) ∧
      ∀ a ∈ E ⊔ zpowers y, a ≠ 1 →
        ⁅M, (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
            (centralizer ({a} : Set X)).subtype ⊓ centralizer ({c} : Set X)⁆ ≤
          (pPrimeCore 2 ↥(centralizer ({c} : Set X))).map (centralizer ({c} : Set X)).subtype ∧
        ⁅M.map (MulAut.conj t).toMonoidHom, (pPrimeCore 2 ↥(centralizer ({a} : Set X))).map
            (centralizer ({a} : Set X)).subtype ⊓ centralizer ({c} : Set X)⁆ ≤
          (pPrimeCore 2 ↥(centralizer ({c} : Set X))).map (centralizer ({c} : Set X)).subtype := by
  classical
  subst hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc2 : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc
    omega
  have htt := S.t_mul_self
  have ht1 : t ≠ 1 := by
    intro h
    have h1 := S.pair.1.1
    rw [h, orderOf_one] at h1
    omega
  have htcC : t ∈ centralizer ({c} : Set X) := mem_centralizer_singleton_iff.mpr htc
  obtain ⟨Jc, hJcJ, hJcpc, hinv, hsubP, χ, hχ⟩ :=
    exists_fixed_component_of_acts S.pair.1.2.1 S.pair.1.2.2.1 θ hcN hc2 he₀ hce (by omega)
  have hβ : Fintype.card ↥((coreImage θ he₀).supportᶜ : Finset (Fin 11)) = 7 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    omega
  let eJc : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃* alternatingGroup (Fin 7) :=
    χ.trans (Fintype.equivFinOfCardEq hβ).altCongrHom
  have hJcCt : Jc ≤ centralizer ({t} : Set X) := (hJcJ.trans inf_le_left).trans S.pair.1.2.1
  have hJcCc : Jc ≤ centralizer ({c} : Set X) := hJcJ.trans inf_le_right
  have hJcC : Jc ≤ centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X) := le_inf hJcCt hJcCc
  have hJcperf : ⁅Jc, Jc⁆ = Jc := UnbalancedCorr.commutator_eq_of_isPComponent hJcC hJcpc
  have hres := primeResidual_eq_top_of_isPComponent hJcC hJcpc
  have hCne : centralizer ({c} : Set X) ≠ ⊤ := centralizer_ne_top_of_ne_one S.nonab hc1
  have hK : SectionRank.IsKGroupCat ↥(centralizer ({c} : Set X)) :=
    UnbalancedCorr.isKGroupCat_of_ne_top S.kProper hCne
  have hTY : Jc ≤ centralizer ({c} : Set X) ⊓ centralizer ({t} : Set X) := by
    rw [inf_comm]
    exact hJcC
  have hTpc : IsPComponent 2
      (Jc.subgroupOf (centralizer ({c} : Set X) ⊓ centralizer ({t} : Set X))) := by
    rw [inf_comm]
    exact hJcpc
  obtain ⟨M, hMC, hMpc, hJcM, hJcMpc, htype⟩ :=
    pump_type_in hPump hK htcC S.pair.1.1 hTY hTpc (by decide) (le_refl 7) eJc
  have hMperf : ⁅M, M⁆ = M := UnbalancedCorr.commutator_eq_of_isPComponent hMC hMpc
  have hJcK : ¬ Jc ≤ UnbalancedLayer.coreActionKernel M := by
    by_cases hfix : M.map (MulAut.conj t).toMonoidHom = M
    · have hJcM' : Jc ≤ M := by
        have h1 := hJcM
        rwa [hfix, sup_idem] at h1
      exact not_le_coreActionKernel_of_le hJcM' hJcperf (nontrivial_coreQuot_of_seven eJc)
    · exact not_le_coreActionKernel_of_pump hMC hMpc htcC hJcM hJcCt hJcperf
        (nontrivial_coreQuot_of_seven eJc) hfix
  refine ⟨Jc, M, hJcJ, hinv, hMC, hMpc, hJcM, hJcK, fun g hgN hgc hgs =>
    mem_normalizer_of_fixed_component θ hJcCc hres hinv hsubP hgN hgc hgs, fun a ha ha1 => ?_⟩
  set Cc : Subgroup X := centralizer ({c} : Set X) with hCcdef
  set Ca : Subgroup X := centralizer ({a} : Set X) with hCadef
  set Oc := (pPrimeCore 2 ↥Cc).map Cc.subtype with hOcdef
  set Oa := (pPrimeCore 2 ↥Ca).map Ca.subtype with hOadef
  have ha2 := S.mul_self_of_mem ha
  have hao : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  have hac : a * c = c * a := mem_centralizer_iff.mp hcB a ha
  have hat : a * t = t * a := (S.t_comm ha).symm
  have hCaN : Ca ≤ normalizer (Oa : Set X) := Sol78.le_normalizer_map_subtype (pPrimeCore 2 ↥Ca)
  have hCcN : Cc ≤ normalizer (Oc : Set X) := Sol78.le_normalizer_map_subtype (pPrimeCore 2 ↥Cc)
  have htCa : t ∈ Ca := mem_centralizer_singleton_iff.mpr hat.symm
  have hXn : ∀ g ∈ Ca ⊓ Cc, ∀ x ∈ Oa ⊓ Cc, g * x * g⁻¹ ∈ Oa ⊓ Cc := by
    intro g hg x hx
    obtain ⟨hga, hgc⟩ := mem_inf.mp hg
    obtain ⟨hxa, hxc⟩ := mem_inf.mp hx
    exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (hCaN hga) x).mp hxa,
      mul_mem (mul_mem hgc hxc) (inv_mem hgc)⟩
  have htX : ∀ x ∈ Oa ⊓ Cc, t * x * t⁻¹ ∈ Oa ⊓ Cc := fun x hx =>
    hXn t (mem_inf.mpr ⟨htCa, htcC⟩) x hx
  have hXodd : Odd (Nat.card ↥(Oa ⊓ Cc)) := by
    have h1 : Odd (Nat.card Oa) := by
      rw [hOadef, card_map_of_injective Ca.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact h1.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hXa : Oa ⊓ Cc ≤ Ca := inf_le_left.trans (map_subtype_le _)
  obtain ⟨ρJ, hρJ⟩ := exists_isPermAction (M := J) (by norm_num) (by norm_num) θ
  have haJN := S.mem_normalizer ha
  have hρJa : 5 ≤ 11 - (ρJ ⟨a, haJN⟩).support.card := by
    obtain ⟨e₁, he₁, hae₁⟩ := S.exists_acts_like_E ha
    have hsplit : ρJ ⟨a, haJN⟩ = ρJ ⟨a * e₁⁻¹, hae₁.1⟩ * ρJ ⟨e₁, le_normalizer (S.le he₁)⟩ := by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      change a = a * e₁⁻¹ * e₁
      group
    have h2 : ρJ ⟨e₁, le_normalizer (S.le he₁)⟩ = coreImage θ (S.le he₁) :=
      hρJ.apply_of_mem (by norm_num) ⟨e₁, S.le he₁⟩
    rw [hsplit, hρJ.eq_one_of_mem_coreActionKernel (by norm_num) hae₁, one_mul, h2]
    have h1 := Finset.card_le_card (S.supp e₁ (S.le he₁) he₁)
    rw [S.card] at h1
    omega
  have hY : ∀ z ∈ Oa ⊓ Cc, t * z = z * t → z ∈ UnbalancedLayer.coreActionKernel Jc := by
    intro z hz hzt
    obtain ⟨hza, hzc⟩ := mem_inf.mp hz
    exact mem_coreActionKernel_of_fixed_balance hbal ht1 htt S.pair.1.2.1 S.pair.1.2.2.1 θ hρJ
      haJN ha2 ha1 hat hρJa he₀ hJcJ hres hinv hsubP
      (mem_inf.mpr ⟨hza, mem_centralizer_singleton_iff.mpr hzt.symm⟩)
      (mem_centralizer_singleton_iff.mp hzc)
  obtain ⟨j, hj, haj, hjs⟩ := S.exists_acts_like hcB he₀ hJcJ hinv hsubP hres hτc hdich χ hχ ha
  have hbalM : ⁅M, Oa ⊓ Cc⁆ ≤ Oc := by
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
    rcases htype with ⟨hfix, ⟨m', hm', hkm', ⟨eM'⟩⟩ | ⟨-, ⟨eHe⟩⟩⟩ | ⟨hne, ⟨eM'⟩⟩
    · have htN : t ∈ normalizer (M : Set X) := mem_normalizer_iff_map_conj_eq.mpr hfix
      have hJcM' : Jc ≤ M := by
        have h1 := hJcM
        rwa [hfix, sup_idem] at h1
      have hJcMpc' : IsPComponent 2 (Jc.subgroupOf (M ⊓ centralizer ({t} : Set X))) := by
        have h1 := hJcMpc
        rwa [hfix, sup_idem] at h1
      by_cases h9 : 9 ≤ m'
      · have hZM : Open.fusionZStar ↥M = pPrimeCore 2 ↥M := by
          have hMC' : M ≤ centralizer ((zpowers c : Subgroup X) : Set X) := by
            rw [hCc']
            exact hMC
          have hMpc' : IsPComponent 2
              (M.subgroupOf (centralizer ((zpowers c : Subgroup X) : Set X))) := by
            rw [hCc']
            exact hMpc
          exact hN1 X S.nonab S.kProper S.unbal S.notU (zpowers c) m' M hT
            (isPGroup_zpowers_of_mul_self hc2) hm' h9 hMC' hMpc' ⟨eM'⟩
        let θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m') :=
          (QuotientGroup.quotientMulEquivOfEq hZM).symm.trans eM'
        exact hX (le_coreActionKernel_of_exact_pump_seven h9 hm' θM htN htt hJcM' hJcCt hJcMpc'
          hres hJcperf hβ χ haM ha2 hj haj hjs hXodd hXNM inf_le_left htX hY)
      · have hm7 : m' = 7 := by
          obtain ⟨k, hk⟩ := hm'
          omega
        subst hm7
        exact hX (le_coreActionKernel_of_trivial_pump htt htN hJcM' hJcCt hJcperf hres eJc
          hMperf eM' hXodd hXNM htX hY)
    · have hJcM' : Jc ≤ M := by
        have h1 := hJcM
        rwa [hfix, sup_idem] at h1
      have hJcMpc' : IsPComponent 2 (Jc.subgroupOf (M ⊓ centralizer ({t} : Set X))) := by
        have h1 := hJcMpc
        rwa [hfix, sup_idem] at h1
      by_cases hinner : ∃ m ∈ M, m⁻¹ * a ∈ UnbalancedLayer.coreActionKernel M
      · obtain ⟨m, hm, hma⟩ := hinner
        exact hX (le_coreActionKernel_of_held_pump hMC hMperf eHe hm haM ha2 hma haK hXodd hXNM
          hXa hXn)
      · push Not at hinner
        exact (hHe X S.nonab S.kProper S.unbal S.notU t J S.pair θ c e₀ he₀ hc htc hcN hce hs4
          Jc M hJcJ hJcpc ⟨eJc⟩ hMC hMpc hfix hJcM' hJcMpc' a hao hac hMX hinner).false eHe
    · exact hX (le_coreActionKernel_of_diagonal_pump hMC hMpc htcC htt hne eM' hJcM hJcCt
        hJcperf hres eJc haM ha2 haK hj haj hXodd hXNM hXa htX hXn hY)
  refine ⟨hbalM, ?_⟩
  have hXt : (Oa ⊓ Cc).map (MulAut.conj t).toMonoidHom = Oa ⊓ Cc :=
    mem_normalizer_iff_map_conj_eq.mp (inf_mem_normalizer' (hCaN htCa) (le_normalizer htcC))
  have hOt : Oc.map (MulAut.conj t).toMonoidHom = Oc :=
    mem_normalizer_iff_map_conj_eq.mp (hCcN htcC)
  calc ⁅M.map (MulAut.conj t).toMonoidHom, Oa ⊓ Cc⁆ =
      ⁅M.map (MulAut.conj t).toMonoidHom, (Oa ⊓ Cc).map (MulAut.conj t).toMonoidHom⁆ := by
        rw [hXt]
    _ = ⁅M, Oa ⊓ Cc⁆.map (MulAut.conj t).toMonoidHom := by rw [map_commutator]
    _ ≤ Oc.map (MulAut.conj t).toMonoidHom := map_mono hbalM
    _ = Oc := hOt

end Sol33

end CFSG.ComponentClassification.SolMax
