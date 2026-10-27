module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallI
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallD
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallH

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem coreImage_ne_one_of_involution [Finite X] {J : Subgroup X} {n : ℕ}
    (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)) {e : X} (he : e ∈ J)
    (he2 : e * e = 1) (he1 : e ≠ 1) : coreImage θ he ≠ 1 := by
  intro h
  have h1 : θ ((⟨e, he⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := Subtype.ext h
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  have hodd : Odd (orderOf (⟨e, he⟩ : ↥J)) := by
    have h2 : orderOf (⟨⟨e, he⟩, h1⟩ : ↥(pPrimeCore 2 ↥J)) ∣ Nat.card (pPrimeCore 2 ↥J) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h2
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h2
  have h3 : orderOf (⟨e, he⟩ : ↥J) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact he2) he1
  rw [h3] at hodd
  exact absurd hodd (by decide)

theorem core_inf_centralizer_le_of_eleven
    (hbal : Sol78.BalanceTwoComponentInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X}
    (hJ : SolAltLit.IsAltTwoComponent t J 11)
    (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin 11))
    {e f : X} (he : e ∈ J) (hf : f ∈ J) (he2 : e * e = 1) (hf2 : f * f = 1) (he1 : e ≠ 1)
    (hf1 : f ≠ 1) (hef : e * f = f * e) (hse : (coreImage θ he).support.card ≤ 4)
    (hsf : (coreImage θ hf).support.card ≤ 4)
    (hdisj : Disjoint (coreImage θ he).support (coreImage θ hf).support) :
    (pPrimeCore 2 (centralizer ({f} : Set X))).map (centralizer ({f} : Set X)).subtype ⊓
        centralizer ({e} : Set X) ≤
      (pPrimeCore 2 (centralizer ({e} : Set X))).map (centralizer ({e} : Set X)).subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ht2, hJC, hJpc, -⟩ := hJ
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    omega
  set Ce : Subgroup X := centralizer ({e} : Set X) with hCedef
  set Cf : Subgroup X := centralizer ({f} : Set X) with hCfdef
  set Oe := (pPrimeCore 2 ↥Ce).map Ce.subtype with hOedef
  set Of := (pPrimeCore 2 ↥Cf).map Cf.subtype with hOfdef
  have hte : t ∈ Ce := by
    rw [hCedef, mem_centralizer_singleton_iff]
    exact (mem_centralizer_singleton_iff.mp (hJC he)).symm
  have htf : t ∈ Cf := by
    rw [hCfdef, mem_centralizer_singleton_iff]
    exact (mem_centralizer_singleton_iff.mp (hJC hf)).symm
  have hCene : Ce ≠ ⊤ := centralizer_ne_top_of_ne_one hnab he1
  have hK : SectionRank.IsKGroupCat ↥Ce := UnbalancedCorr.isKGroupCat_of_ne_top hKP hCene
  by_contra hX₀
  have he2' : e ^ 2 = 1 := by rw [sq]; exact he2
  have hf2' : f ^ 2 = 1 := by rw [sq]; exact hf2
  have hS : zpowers f ≠ ⊥ := fun h => hf1 (zpowers_eq_bot.mp h)
  have hT : zpowers e ≠ ⊥ := fun h => he1 (zpowers_eq_bot.mp h)
  have hST : zpowers f ≤ centralizer ((zpowers e : Subgroup X) : Set X) := by
    rw [centralizer_zpowers_eq', zpowers_le, mem_centralizer_singleton_iff]
    exact hef.symm
  obtain ⟨-, hbc, hd⟩ := hbal X (zpowers f) (zpowers e) hS hT
    (IsElementaryAbelian.zpowers_of_pow_eq_one hf2')
    (IsElementaryAbelian.zpowers_of_pow_eq_one he2') hST
  have hCe' : centralizer ((zpowers e : Subgroup X) : Set X) = Ce := centralizer_zpowers_eq' e
  have hCf' : centralizer ((zpowers f : Subgroup X) : Set X) = Cf := centralizer_zpowers_eq' f
  rw [hCe', hCf'] at hbc hd
  obtain ⟨M, ⟨hMCe, hMpc⟩, hMX⟩ := hd hX₀
  obtain ⟨hX₀N, hc⟩ := hbc M ⟨hMCe, hMpc⟩
  obtain ⟨hfN', -, hOM⟩ := hc hMX
  have hfM : f ∈ normalizer (M : Set X) := by
    obtain ⟨⟨g, hg⟩, hg1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hfN'
    obtain ⟨hgf, hgN⟩ := mem_inf.mp hg
    rcases eq_one_or_eq_of_mem_zpowers hf2 hgf with h | h
    · exact absurd (Subtype.ext h) hg1
    · exact h ▸ hgN
  have hOMCe : (pPrimeCore 2 ↥M).map M.subtype ≤ Oe := pPrimeCore_le_of_isPComponent hMCe hMpc
  have hfK : f ∉ UnbalancedLayer.coreActionKernel M := by
    intro hfK
    have h1 : ⁅M, zpowers f ⊓ normalizer (M : Set X)⁆ ≤ Oe :=
      (commutator_le_of_le_coreActionKernel (inf_le_left.trans (zpowers_le.mpr hfK))).trans
        hOMCe
    have h2 : Oe ⊔ M ≤ Oe := by
      have h3 : GH74.GLS.pPrimeCoreOf 2 Ce ⊔ M = GH74.GLS.pPrimeCoreOf 2 Ce ⊔
          ⁅M, zpowers f ⊓ normalizer (M : Set X)⁆ := hOM
      change GH74.GLS.pPrimeCoreOf 2 Ce ⊔ M ≤ GH74.GLS.pPrimeCoreOf 2 Ce
      rw [h3]
      exact sup_le le_rfl h1
    exact not_le_pPrimeCore_of_isPComponent hMCe hMpc (le_sup_right.trans h2)
  have hMX' : ¬ Of ⊓ Ce ≤ UnbalancedLayer.coreActionKernel M := fun hK' =>
    hMX ((commutator_le_of_le_coreActionKernel hK').trans hOMCe)
  have hθe1 := coreImage_ne_one_of_involution θ he he2 he1
  have hθe2 : coreImage θ he * coreImage θ he = 1 := by
    have h1 : (⟨e, he⟩ : ↥J) * ⟨e, he⟩ = 1 := Subtype.ext he2
    have h2 : θ ((⟨e, he⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) *
        θ ((⟨e, he⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := by
      rw [← map_mul, ← QuotientGroup.mk_mul, h1, QuotientGroup.mk_one, map_one]
    exact congrArg Subtype.val h2
  have hse4 : 4 ≤ (coreImage θ he).support.card :=
    four_le_card_support_of_mem_alternatingGroup (coreImage_mem θ he) hθe2 hθe1
  have heN : e ∈ normalizer (J : Set X) := le_normalizer he
  have hee : e * e⁻¹ ∈ UnbalancedLayer.coreActionKernel J := by
    rw [mul_inv_cancel]
    exact one_mem _
  obtain ⟨Je, hJeJC, hJepc, hinv, hsubP, χ, hχ⟩ :=
    exists_fixed_component_of_acts hJC hJpc θ heN he2 he hee (by omega)
  have hJeCe : Je ≤ Ce := hJeJC.trans inf_le_right
  have hJeJ : Je ≤ J := hJeJC.trans inf_le_left
  have hfJe : f ∈ Je := by
    refine hinv f hf hef.symm ⟨1, by rw [pow_one, sq]; exact hf2⟩ ?_
    intro x hx
    rw [Finset.mem_compl]
    exact Finset.disjoint_right.mp hdisj hx
  have hcardβ : Fintype.card ↥((coreImage θ he).supportᶜ : Finset (Fin 11)) = 7 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
    omega
  let eJe : ↥Je ⧸ pPrimeCore 2 ↥Je ≃* alternatingGroup (Fin 7) :=
    χ.trans (Fintype.equivFinOfCardEq hcardβ).altCongrHom
  have hJeTC : Je ≤ Ce ⊓ centralizer ({t} : Set X) := le_inf hJeCe (hJeJ.trans hJC)
  have hJepc' : IsPComponent 2 (Je.subgroupOf (Ce ⊓ centralizer ({t} : Set X))) := by
    rw [inf_comm]
    exact hJepc
  have hJeperf : ⁅Je, Je⁆ = Je :=
    UnbalancedCorr.commutator_eq_of_isPComponent (le_inf (hJeJ.trans hJC) hJeCe) hJepc
  have hres := primeResidual_eq_top_of_isPComponent (le_inf (hJeJ.trans hJC) hJeCe) hJepc
  obtain ⟨M', hM'Ce, hM'pc, hJeM', hJeM'pc, htype⟩ :=
    pump_type_in hPump hK hte ht2 hJeTC hJepc' (by decide) (le_refl 7) eJe
  set M't := M'.map (MulAut.conj t).toMonoidHom with hM'tdef
  obtain ⟨hM'tCe, hM'tpc⟩ := isPComponent_conj hM'Ce hM'pc hte
  have hMM' : M = M' ∨ M = M't := by
    by_contra h
    push Not at h
    have h1 : M' ≤ UnbalancedLayer.coreActionKernel M :=
      GSThmB.B5a.le_coreActionKernel_of_ne hMCe hM'Ce hMpc hM'pc h.1
    have h2 : M't ≤ UnbalancedLayer.coreActionKernel M :=
      GSThmB.B5a.le_coreActionKernel_of_ne hMCe hM'tCe hMpc hM'tpc h.2
    exact hfK ((sup_le h1 h2) (hJeM' hfJe))
  have hMperf : ⁅M, M⁆ = M := UnbalancedCorr.commutator_eq_of_isPComponent hMCe hMpc
  have hX₀NM : Of ⊓ Ce ≤ normalizer (M : Set X) :=
    le_normalizer_of_le_normalizer_sup hMCe hMpc inf_le_right hX₀N
  have hX₀odd : Odd (Nat.card ↥(Of ⊓ Ce)) := by
    have h1 : Odd (Nat.card Of) := by
      rw [hOfdef, card_map_of_injective Cf.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact h1.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hCfN : Cf ≤ normalizer (Of : Set X) := Sol78.le_normalizer_map_subtype (pPrimeCore 2 ↥Cf)
  have hX₀n : ∀ g ∈ Cf ⊓ Ce, ∀ x ∈ Of ⊓ Ce, g * x * g⁻¹ ∈ Of ⊓ Ce := by
    intro g hg x hx
    obtain ⟨hgf, hge⟩ := mem_inf.mp hg
    obtain ⟨hxf, hxe⟩ := mem_inf.mp hx
    exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (hCfN hgf) x).mp hxf,
      mul_mem (mul_mem hge hxe) (inv_mem hge)⟩
  have htX : ∀ x ∈ Of ⊓ Ce, t * x * t⁻¹ ∈ Of ⊓ Ce := fun x hx =>
    hX₀n t (mem_inf.mpr ⟨htf, hte⟩) x hx
  have hX₀f : Of ⊓ Ce ≤ Cf := inf_le_left.trans (map_subtype_le _)
  obtain ⟨ρJ, hρJ⟩ := exists_isPermAction (M := J) (by norm_num) (by norm_num) θ
  have hfJN : f ∈ normalizer (J : Set X) := le_normalizer hf
  have hρJf : 5 ≤ 11 - (ρJ ⟨f, hfJN⟩).support.card := by
    have h1 : ρJ ⟨f, hfJN⟩ = coreImage θ hf := hρJ.apply_of_mem (by norm_num) ⟨f, hf⟩
    rw [h1]
    omega
  have hft : f * t = t * f := mem_centralizer_singleton_iff.mp (hJC hf)
  have hY : ∀ y ∈ Of ⊓ Ce, t * y = y * t → y ∈ UnbalancedLayer.coreActionKernel Je := by
    intro y hy hyt
    obtain ⟨hyf, hye⟩ := mem_inf.mp hy
    have hy' : y ∈ Of ⊓ centralizer ({t} : Set X) :=
      mem_inf.mpr ⟨hyf, mem_centralizer_singleton_iff.mpr hyt.symm⟩
    exact mem_coreActionKernel_of_fixed_balance hbal ht1 htt hJC hJpc θ hρJ hfJN hf2 hf1 hft
      hρJf he hJeJC hres hinv hsubP hy' (mem_centralizer_singleton_iff.mp hye)
  have hsf' : f * f⁻¹ ∈ UnbalancedLayer.coreActionKernel Je := by
    rw [mul_inv_cancel]
    exact one_mem _
  rcases htype with ⟨hfix, ⟨m', hm', hkm', ⟨eM'⟩⟩ | ⟨-, ⟨eHe⟩⟩⟩ | ⟨hne, ⟨eM'⟩⟩
  · have hMeq : M = M' := by
      rcases hMM' with h | h
      · exact h
      · rw [h]
        exact hfix
    subst hMeq
    have htN : t ∈ normalizer (M : Set X) := mem_normalizer_iff_map_conj_eq.mpr hfix
    have hJeM : Je ≤ M := by
      have h1 := hJeM'
      rwa [hfix, sup_idem] at h1
    have hJeMpc : IsPComponent 2 (Je.subgroupOf (M ⊓ centralizer ({t} : Set X))) := by
      have h1 := hJeM'pc
      rwa [hfix, sup_idem] at h1
    by_cases h9 : 9 ≤ m'
    ·
      have hZM : Open.fusionZStar ↥M = pPrimeCore 2 ↥M := by
        have hMCe' : M ≤ centralizer ((zpowers e : Subgroup X) : Set X) := by
          rw [hCe']
          exact hMCe
        have hMpc' : IsPComponent 2
            (M.subgroupOf (centralizer ((zpowers e : Subgroup X) : Set X))) := by
          rw [hCe']
          exact hMpc
        exact hN1 X hnab hKP hunb hnU (zpowers e) m' M hT (isPGroup_zpowers_of_mul_self he2) hm'
          h9 hMCe' hMpc' ⟨eM'⟩
      let θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m') :=
        (QuotientGroup.quotientMulEquivOfEq hZM).symm.trans eM'
      obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θM
      have hJeN : Je ≤ normalizer (M : Set X) := hJeM.trans le_normalizer
      have hρf : ρ ⟨f, hJeN hfJe⟩ ≠ 1 := fun h => hfK (hρ.mem_coreActionKernel _ h)
      have hsupp := card_support_action_le (le_refl 7) hkm' (by omega) θM hρ hJeN hres
        hJeperf hcardβ χ hfJe hρf (Or.inr ⟨t, htN, htt, hJeM, hJeJ.trans hJC, hJeMpc⟩)
      have hσ4 : (ρ ⟨f, hfM⟩).support.card ≤ 4 := by
        have h1 := hχ ⟨f, hfJe⟩ hf
        have h2 : (ρ ⟨f, hfM⟩).support.card = (ρ ⟨f, hJeN hfJe⟩).support.card := rfl
        rw [h2, hsupp, ← card_support_ofSubtype, h1]
        exact hsf
      exact hMX' (hρ.le_coreActionKernel hfM hf2 hσ4 (by omega) hX₀NM inf_le_left)
    ·
      have hm7 : m' = 7 := by
        obtain ⟨a, ha⟩ := hm'
        omega
      subst hm7
      exact hMX' (le_coreActionKernel_of_trivial_pump htt htN hJeM (hJeJ.trans hJC) hJeperf
        hres eJe hMperf eM' hX₀odd hX₀NM htX hY)
  ·
    have hMeq : M = M' := by
      rcases hMM' with h | h
      · exact h
      · rw [h]
        exact hfix
    subst hMeq
    have hJeM : Je ≤ M := by
      have h1 := hJeM'
      rwa [hfix, sup_idem] at h1
    have hff : f⁻¹ * f ∈ UnbalancedLayer.coreActionKernel M := by
      rw [inv_mul_cancel]
      exact one_mem _
    exact hMX' (le_coreActionKernel_of_held_pump hMCe hMperf eHe (hJeM hfJe) hfM hf2 hff hfK
      hX₀odd hX₀NM hX₀f hX₀n)
  ·
    have hdiag : M.map (MulAut.conj t).toMonoidHom ≠ M ∧
        Je ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom ∧
        Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin 7)) := by
      rcases hMM' with h | h
      · subst h
        exact ⟨hne, hJeM', ⟨eM'⟩⟩
      · subst h
        let φt : ↥M' ≃* ↥M't := M'.equivMapOfInjective _ (MulAut.conj t).injective
        refine ⟨?_, ?_, ⟨(Sol78.fusionZStarQuotCongr φt).symm.trans eM'⟩⟩
        · rw [hM'tdef, map_conj_map_conj_of_mul_self htt]
          exact fun h => hne h.symm
        · rw [hM'tdef, map_conj_map_conj_of_mul_self htt, sup_comm]
          exact hJeM'
    obtain ⟨hMne, hJeMM, ⟨eMZ⟩⟩ := hdiag
    exact hMX' (le_coreActionKernel_of_diagonal_pump hMCe hMpc hte htt hMne eMZ hJeMM
      (hJeJ.trans hJC) hJeperf hres eJe hfM hf2 hfK hfJe hsf' hX₀odd hX₀NM hX₀f htX hX₀n hY)

end CFSG.ComponentClassification.SolMax
