module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32G

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem not_le_pPrimeCore_of_isPComponent [Finite X] {L C : Subgroup X} (hLC : L ≤ C)
    (hL : IsPComponent 2 (L.subgroupOf C)) : ¬ L ≤ (pPrimeCore 2 ↥C).map C.subtype := by
  intro hLO
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L C hLC).mp hL).2.2
  have hodd : Nat.Coprime 2 (Nat.card L) := by
    have h1 : Nat.card L ∣ Nat.card ((pPrimeCore 2 ↥C).map C.subtype) := card_dvd_of_le hLO
    rw [card_map_of_injective C.subtype_injective] at h1
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  have htop : pPrimeCore 2 ↥L = ⊤ := by
    rw [eq_top_iff]
    exact le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩
  have : Nontrivial (↥L ⧸ pPrimeCore 2 ↥L) := LocalCores.isQuasisimple_nontrivial hLq
  have : Subsingleton (↥L ⧸ pPrimeCore 2 ↥L) := QuotientGroup.subsingleton_iff.mpr htop
  exact false_of_nontrivial_of_subsingleton (↥L ⧸ pPrimeCore 2 ↥L)

theorem commutator_le_of_le_coreActionKernel {M Y : Subgroup X}
    (hY : Y ≤ UnbalancedLayer.coreActionKernel M) : ⁅M, Y⁆ ≤ (pPrimeCore 2 ↥M).map M.subtype := by
  rw [commutator_le]
  intro m hm g hg
  have h2 := (UnbalancedLayer.mem_coreActionKernel.mp (hY (inv_mem hg))).2 m⁻¹ (inv_mem hm)
  rw [commutatorElement_def]
  have h3 : m⁻¹⁻¹ * g⁻¹⁻¹ * m⁻¹ * g⁻¹ = m * g * m⁻¹ * g⁻¹ := by group
  rwa [h3] at h2

theorem centralizer_ne_top_of_ne_one [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) {e : X}
    (he1 : e ≠ 1) : centralizer ({e} : Set X) ≠ ⊤ := by
  intro h
  have hec : e ∈ center X := by
    rw [mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({e} : Set X) := h ▸ mem_top g
    exact mem_centralizer_singleton_iff.mp hg
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h' | h'
  · rw [h', mem_bot] at hec
    exact he1 hec
  · obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have ha : a ∈ center X := h' ▸ mem_top a
    exact (mem_center_iff.mp ha b).symm

theorem eq_one_or_eq_of_mem_zpowers {f g : X} (hf2 : f * f = 1) (hg : g ∈ zpowers f) :
    g = 1 ∨ g = f := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  have hf2' : f ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hf2
  rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · left
    rw [hj, ← two_mul, zpow_mul, hf2', one_zpow]
  · right
    rw [hj, zpow_add, zpow_mul, hf2', one_zpow, one_mul, zpow_one]

theorem core_inf_centralizer_le_of_large (hbal : Sol78.BalanceTwoComponentInput)
    (hPump : Sol78.AlternatingPumpUpInput) (hN1 : TwoGroupAltCoverExclusion) [Finite X]
    [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X} {n : ℕ}
    (hJ : SolAltLit.IsAltTwoComponent t J n)
    (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)) (hn : 13 ≤ n) (hnodd : Odd n)
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
  set Ce : Subgroup X := centralizer ({e} : Set X) with hCedef
  set Cf : Subgroup X := centralizer ({f} : Set X) with hCfdef
  set Oe := (pPrimeCore 2 ↥Ce).map Ce.subtype with hOedef
  set Of := (pPrimeCore 2 ↥Cf).map Cf.subtype with hOfdef
  have hte : t ∈ Ce := by
    rw [hCedef, mem_centralizer_singleton_iff]
    exact (mem_centralizer_singleton_iff.mp (hJC he)).symm
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
    (IsElementaryAbelian.zpowers_of_pow_eq_one he2')
    hST
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
  have hθe2 : coreImage θ he * coreImage θ he = 1 := by
    have h1 : (⟨e, he⟩ : ↥J) * ⟨e, he⟩ = 1 := Subtype.ext he2
    have h2 : θ ((⟨e, he⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) *
        θ ((⟨e, he⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := by
      rw [← map_mul, ← QuotientGroup.mk_mul, h1, QuotientGroup.mk_one, map_one]
    exact congrArg Subtype.val h2
  have hev : 2 ∣ (coreImage θ he).support.card :=
    Perm.two_dvd_card_support (by rw [sq]; exact hθe2)
  set k := n - (coreImage θ he).support.card with hkdef
  have hk9 : 9 ≤ k := by omega
  have hkodd : Odd k := by
    obtain ⟨a, ha⟩ := hnodd
    obtain ⟨b, hb⟩ := hev
    exact ⟨a - b, by omega⟩
  obtain ⟨Je, hJeJC, hJepc, hinv, χ, hχ⟩ :=
    exists_inner_fixed_component hJC hJpc θ he he2 (by omega)
  have hJeCe : Je ≤ Ce := hJeJC.trans inf_le_right
  have hJeJ : Je ≤ J := hJeJC.trans inf_le_left
  have hfJe : f ∈ Je := by
    refine hinv f hf hef.symm hf2 ?_
    intro x hx
    rw [Finset.mem_compl]
    exact Finset.disjoint_right.mp hdisj hx
  have hcardβ : Fintype.card ↥((coreImage θ he).supportᶜ : Finset (Fin n)) = k := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  let eJe : ↥Je ⧸ pPrimeCore 2 ↥Je ≃* alternatingGroup (Fin k) :=
    χ.trans (Fintype.equivFinOfCardEq hcardβ).altCongrHom
  have hJeTC : Je ≤ Ce ⊓ centralizer ({t} : Set X) := le_inf hJeCe (hJeJ.trans hJC)
  have hJepc' : IsPComponent 2 (Je.subgroupOf (Ce ⊓ centralizer ({t} : Set X))) := by
    rw [inf_comm]
    exact hJepc
  obtain ⟨M', hM'Ce, hM'pc, hJeM', hJeM'pc, htype⟩ :=
    pump_type_in hPump hK hte ht2 hJeTC hJepc' hkodd (by omega) eJe
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
  have hM'tN : M't ≤ normalizer (M' : Set X) ∧ M' ≤ normalizer (M't : Set X) := by
    by_cases hfix : M't = M'
    · rw [hfix]
      exact ⟨le_normalizer, le_normalizer⟩
    · exact ⟨fun x hx => (GSThmB.B5a.le_coreActionKernel_of_ne hM'Ce hM'tCe hM'pc hM'tpc
        (Ne.symm hfix) hx).1, fun x hx => (GSThmB.B5a.le_coreActionKernel_of_ne hM'tCe hM'Ce
        hM'tpc hM'pc hfix hx).1⟩
  have hJeN : Je ≤ normalizer (M : Set X) := by
    refine hJeM'.trans (sup_le ?_ ?_)
    · rcases hMM' with rfl | rfl
      · exact le_normalizer
      · exact hM'tN.2
    · rcases hMM' with rfl | rfl
      · exact hM'tN.1
      · exact le_normalizer
  let φt : ↥M' ≃* ↥M't := M'.equivMapOfInjective _ (MulAut.conj t).injective
  have hshape : ∃ r : ℕ, Odd r ∧ k ≤ r ∧
      Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin r)) ∧
      (r = k ∨ ∃ s : X, s ∈ normalizer (M : Set X) ∧ s * s = 1 ∧ Je ≤ M ∧
        Je ≤ centralizer ({s} : Set X) ∧
        IsPComponent 2 (Je.subgroupOf (M ⊓ centralizer ({s} : Set X)))) := by
    rcases htype with ⟨hfix, ⟨m', hm', hkm', ⟨eM'⟩⟩ | ⟨h7, -⟩⟩ | ⟨-, ⟨eM'⟩⟩
    · have hMeq : M = M' := by
        rcases hMM' with h | h
        · exact h
        · rw [h]
          exact hfix
      subst hMeq
      have htN : t ∈ normalizer (M : Set X) := mem_normalizer_iff_map_conj_eq.mpr hfix
      rw [hfix, sup_idem] at hJeM' hJeM'pc
      exact ⟨m', hm', hkm', ⟨eM'⟩, Or.inr ⟨t, htN, htt, hJeM', hJeJ.trans hJC, hJeM'pc⟩⟩
    · omega
    · refine ⟨k, hkodd, le_rfl, ?_, Or.inl rfl⟩
      rcases hMM' with h | h
      · subst h
        exact ⟨eM'⟩
      · subst h
        exact ⟨(Sol78.fusionZStarQuotCongr φt).symm.trans eM'⟩
  obtain ⟨r, hr, hkr, ⟨eMZ⟩, hcase⟩ := hshape
  have hZM : Open.fusionZStar ↥M = pPrimeCore 2 ↥M := by
    have hMCe' : M ≤ centralizer ((zpowers e : Subgroup X) : Set X) := by rw [hCe']; exact hMCe
    have hMpc' : IsPComponent 2 (M.subgroupOf (centralizer ((zpowers e : Subgroup X) : Set X))) :=
      by rw [hCe']; exact hMpc
    exact hN1 X hnab hKP hunb hnU (zpowers e) r M hT (isPGroup_zpowers_of_mul_self he2) hr
      (by omega) hMCe' hMpc' ⟨eMZ⟩
  let θM : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin r) :=
    (QuotientGroup.quotientMulEquivOfEq hZM).symm.trans eMZ
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θM
  have hρf : ρ ⟨f, hJeN hfJe⟩ ≠ 1 := fun h => hfK (hρ.mem_coreActionKernel _ h)
  have hJeperf : ⁅Je, Je⁆ = Je :=
    UnbalancedCorr.commutator_eq_of_isPComponent (le_inf (hJeJ.trans hJC) hJeCe) hJepc
  have hsupp := card_support_action_le (by omega) hkr (by omega) θM hρ hJeN
    (primeResidual_eq_top_of_isPComponent (le_inf (hJeJ.trans hJC) hJeCe) hJepc) hJeperf
    hcardβ χ hfJe hρf hcase
  have hσ4 : (ρ ⟨f, hfM⟩).support.card ≤ 4 := by
    have h1 := hχ ⟨f, hfJe⟩ hf
    have h2 : (ρ ⟨f, hfM⟩).support.card = (ρ ⟨f, hJeN hfJe⟩).support.card := rfl
    rw [h2, hsupp, ← card_support_ofSubtype, h1]
    exact hsf
  have hX₀Ce : Of ⊓ Ce ≤ Ce := inf_le_right
  have hX₀NM : Of ⊓ Ce ≤ normalizer (M : Set X) :=
    le_normalizer_of_le_normalizer_sup hMCe hMpc hX₀Ce hX₀N
  have hX₀K := hρ.le_coreActionKernel hfM hf2 hσ4 (by omega) hX₀NM inf_le_left
  exact hMX ((commutator_le_of_le_coreActionKernel hX₀K).trans hOMCe)

end CFSG.ComponentClassification.SolMax
