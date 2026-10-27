module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoRankAux
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentTrichotomy

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

namespace ReducedNongeneration

section Aut

variable {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem _root_.CFSG.AGLEmbedding.CatalogSimpleSections.isSimpleGroup_of_center_eq_bot
    {Y : Type*} [Group Y] (hX : CatalogSimpleSections Y) {K : Subgroup Y} (hK : IsComponentOf K ⊤)
    (hZ : Subgroup.center K = ⊥) :
    IsSimpleGroup K ∧ (∃ a b : K, a * b ≠ b * a) ∧ IsCatalogGroup K := by
  let e : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  refine ⟨e.isSimpleGroup, ?_, IsCatalogGroup.of_mulEquiv e (hX.isCatalogGroup_center_quotient hK)⟩
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2
  refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
  simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba

theorem isSimpleGroup_of_isCyclic {Y : Type} [Group Y] [Finite Y] {Rb : Sylow p Y}
    {Y₀ : Subgroup Y} (h : ReducedNongeneration p Y Rb Y₀)
    (hX : CatalogSimpleSections Y) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (hcyc : IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y)) :
    IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧ IsCatalogGroup L ∧
      ∃ T : Sylow p L, (T : Subgroup L) ≠ ⊥ ∧ IsCyclic (T : Subgroup L) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hsimple, hnonab, hcat⟩ :=
    hX.isSimpleGroup_of_center_eq_bot hL (h.center_eq_bot_of_isCyclic hL hcyc)
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rb
    (ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
      Subgroup.IsSubnormal.top)
  have hTcyc : IsCyclic (T : Subgroup L) := by
    rw [← hT] at hcyc
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective _ _ L.subtype_injective).symm (MulEquiv.surjective _)
  obtain ⟨t, htRL, ht, -⟩ := exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot Rb hL
  refine ⟨hsimple, hnonab, hcat, T, fun hbot => ?_, hTcyc⟩
  rw [hbot, Subgroup.map_bot] at hT
  have ht1 : t ∈ (⊥ : Subgroup Y) := by
    rw [hT]
    exact htRL
  rw [Subgroup.mem_bot] at ht1
  rw [ht1, orderOf_one] at ht
  exact hp.one_lt.ne ht

theorem pRank_mulAut_le_two_of_isCyclic (h : ReducedNongeneration p X R X₀)
    (hX : CatalogSimpleSections X) (hKF : KFactBeta) {L : Subgroup X}
    (hL : IsComponentOf L ⊤) (hcyc : IsCyclic ((R : Subgroup X) ⊓ L : Subgroup X)) :
    Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ 2 := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨hsimple, hnonab, hcat, T, hTne, hTcyc⟩ := h.isSimpleGroup_of_isCyclic hX hL hcyc
  rcases hKF L hsimple hnonab hcat p h.prime h.ne_two T hTne (Or.inl hTcyc) with hAut | hfacts
  · exact hAut
  · exact pRank_mulAut_le_two_of_kOutRankLeOne h.prime (h.center_eq_bot_of_isCyclic hL hcyc)
      (fun A hA => card_le_of_isElemAbelian_of_isCyclic_sylow T hTcyc hA) hfacts.1

end Aut

section Frattini

variable {p : ℕ} {X : Type*} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem false_of_normalizer_inf_generalizedFitting_le (h : ReducedNongeneration p X R X₀)
    (hall : ∀ L : Subgroup X, IsComponentOf L ⊤ → L ≤ X₀) {Q : Subgroup X}
    (hQR : Q ≤ R) (hQ : 2 ≤ Open.pRank p Q)
    (hC : 3 ≤ Open.pRank p ((R : Subgroup X) ⊓ Subgroup.centralizer (Q : Set X)))
    (hN : Subgroup.normalizer
        (((R : Subgroup X) ⊓ CFSG.generalizedFitting X : Subgroup X) : Set X) ≤
      Subgroup.normalizer (Q : Set X)) : False := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : (CFSG.generalizedFitting X).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  have : (CFSG.pCore p X).Normal := CFSG.pCore_normal
  have hNQ : Subgroup.normalizer (Q : Set X) ≤ X₀ :=
    (normalizer_le_weakCore p hQR hQ
      (hC.trans (PreuniquenessRankFour.Helpers.pRank_mono p hp le_sup_right))).trans
      h.weakCore_le
  refine not_le_of_normalizer_inf_le R (hN.trans hNQ) h.ne_top (sup_le ?_ ?_)
  · rw [CFSG.Fitting_eq_pcore X p h.core_eq_bot]
    exact (CFSG.pCore_isPGroup.le_sylow_of_normal R).trans h.sylow_le
  · exact sSup_le fun L hL => hall L ((CFSG.isComponent_iff_open L).mp hL)

theorem three_le_pRank_inf_centralizer_sup_zpowers (h : ReducedNongeneration p X R X₀)
    {a b : X} (ha : orderOf a = p) (hb : orderOf b = p)
    (haR : ∀ v ∈ (R : Subgroup X), v * a * v⁻¹ ∈ Subgroup.zpowers a)
    (hbR : ∀ v ∈ (R : Subgroup X), v * b * v⁻¹ ∈ Subgroup.zpowers b) :
    3 ≤ Open.pRank p ((R : Subgroup X) ⊓
      Subgroup.centralizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup X) : Set X)) := by
  have hp := h.prime
  obtain ⟨A, hAR, hA, hAcard⟩ := pRank_attained p hp (R : Subgroup X)
  refine h.three_le_pRank.trans (le_csSup (pRank_bddAbove p hp _) ⟨A, le_inf hAR
    (le_centralizer_sup_zpowers (fun v hv => ?_) (fun v hv => ?_)), hA, hAcard⟩)
  · exact commute_of_mem_normalizer_zpowers_of_pow_eq_one hp ha
      (mem_normalizer_zpowers_of_mem_zpowers (haR v (hAR hv))) (hA.2 v hv)
  · exact commute_of_mem_normalizer_zpowers_of_pow_eq_one hp hb
      (mem_normalizer_zpowers_of_mem_zpowers (hbR v (hAR hv))) (hA.2 v hv)

theorem conj_mem_zpowers_of_component (h : ReducedNongeneration p X R X₀) {L : Subgroup X}
    (hL : IsComponentOf L ⊤) (hcyc : IsCyclic ((R : Subgroup X) ⊓ L : Subgroup X)) {t v : X}
    (ht : t ∈ (R : Subgroup X) ⊓ L) (hv : v ∈ (R : Subgroup X)) :
    v * t * v⁻¹ ∈ Subgroup.zpowers t :=
  conj_mem_zpowers_of_isCyclic rfl ht
    ⟨(R : Subgroup X).mul_mem ((R : Subgroup X).mul_mem hv ht.1) ((R : Subgroup X).inv_mem hv),
      (Subgroup.mem_normalizer_iff.mp (h.sylow_le_normalizer_component hL hv) t).mp ht.2⟩

theorem eq_or_eq_of_isComponentOf (h : ReducedNongeneration p X R X₀) {L₁ L₂ L : Subgroup X}
    (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂)
    (hL : IsComponentOf L ⊤) : L = L₁ ∨ L = L₂ := by
  by_contra hcon
  push Not at hcon
  exact h.false_of_three_components h₁ h₂ hL hne (Ne.symm hcon.1) (Ne.symm hcon.2)

theorem false_of_two_components (h : ReducedNongeneration p X R X₀) {L₁ L₂ : Subgroup X}
    (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂)
    (hcyc : ∀ L : Subgroup X, IsComponentOf L ⊤ → IsCyclic ((R : Subgroup X) ⊓ L : Subgroup X))
    (hall : ∀ L : Subgroup X, IsComponentOf L ⊤ → L ≤ X₀) : False := by
  have hp := h.prime
  obtain ⟨t₁, ⟨ht₁R, ht₁L⟩, ht₁, -⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R h₁
  obtain ⟨t₂, ⟨ht₂R, ht₂L⟩, ht₂, ht₂C⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R h₂
  have h₁₂ := le_centralizer_of_component_ne h₁ h₂ hne
  have hmem : ∀ L : Subgroup X, IsComponentOf L ⊤ → ∀ t ∈ L, orderOf t = p → ∀ g : X,
      g * t * g⁻¹ ∈ (R : Subgroup X) →
        g * t * g⁻¹ ∈ Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ := by
    intro L hL t htL ht g hg
    have hgt : g * t * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := ⟨t, htL, rfl⟩
    rcases h.eq_or_eq_of_isComponentOf h₁ h₂ hne
        ((ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL) with
      heq | heq
    · have := hcyc L₁ h₁
      exact Subgroup.mem_sup_left (conj_mem_zpowers_of_isCyclic (T := (R : Subgroup X) ⊓ L₁)
        (ht.trans ht₁.symm) ⟨ht₁R, ht₁L⟩ ⟨hg, heq ▸ hgt⟩)
    · have := hcyc L₂ h₂
      exact Subgroup.mem_sup_right (conj_mem_zpowers_of_isCyclic (T := (R : Subgroup X) ⊓ L₂)
        (ht.trans ht₂.symm) ⟨ht₂R, ht₂L⟩ ⟨hg, heq ▸ hgt⟩)
  have hQR : Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ ≤ R :=
    sup_le (Subgroup.zpowers_le.mpr ht₁R) (Subgroup.zpowers_le.mpr ht₂R)
  have hQ2 : 2 ≤ Open.pRank p (Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂) :=
    two_le_pRank_of_commute_of_not_mem_zpowers hp ht₁ (ht₂ ▸ pow_orderOf_eq_one t₂)
      (fun ht => ht₂C (Subgroup.zpowers_le.mpr (h₁₂ ht₁L) ht))
      (Subgroup.mem_centralizer_iff.mp (h₁₂ ht₁L) t₂ ht₂L).symm
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers t₁))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers t₂))
  have hC := h.three_le_pRank_inf_centralizer_sup_zpowers ht₁ ht₂
    (fun v hv => h.conj_mem_zpowers_of_component h₁ (hcyc L₁ h₁) ⟨ht₁R, ht₁L⟩ hv)
    (fun v hv => h.conj_mem_zpowers_of_component h₂ (hcyc L₂ h₂) ⟨ht₂R, ht₂L⟩ hv)
  have hF : CFSG.layer X ≤ CFSG.generalizedFitting X := le_sup_right
  refine h.false_of_normalizer_inf_generalizedFitting_le hall hQR hQ2 hC fun g hg =>
    mem_normalizer_sup_zpowers ?_ ?_
  · exact hmem L₁ h₁ t₁ ht₁L ht₁ g ((Subgroup.mem_normalizer_iff.mp hg t₁).mp
      ⟨ht₁R, hF (le_layer_of_isComponentOf h₁ ht₁L)⟩).1
  · exact hmem L₂ h₂ t₂ ht₂L ht₂ g ((Subgroup.mem_normalizer_iff.mp hg t₂).mp
      ⟨ht₂R, hF (le_layer_of_isComponentOf h₂ ht₂L)⟩).1

theorem false_of_unique_component_of_pCore_ne_bot (h : ReducedNongeneration p X R X₀)
    {L : Subgroup X} (hL : IsComponentOf L ⊤)
    (huniq : ∀ L' : Subgroup X, IsComponentOf L' ⊤ → L' = L)
    (hcyc : IsCyclic ((R : Subgroup X) ⊓ L : Subgroup X)) (hLX₀ : L ≤ X₀)
    (hO : CFSG.pCore p X ≠ ⊥) : False := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : (CFSG.pCore p X).Normal := CFSG.pCore_normal
  have : IsCyclic (CFSG.pCore p X) := h.isCyclic_pCore_of_component hL
  have hZ := h.center_eq_bot_of_isCyclic hL hcyc
  obtain ⟨z, hzO, hz, -⟩ := exists_mem_centralizer_orderOf_eq CFSG.pCore_isPGroup hO
  obtain ⟨t, ⟨htR, htL⟩, ht, -⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R hL
  have hEC : CFSG.layer X ≤ Subgroup.centralizer (CFSG.pCore p X : Set X) := by
    rw [← CFSG.Fitting_eq_pcore X p h.core_eq_bot]
    exact Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp CFSG.LocalCores.fitting_layer_commute)
  have hzC : z ∈ Subgroup.centralizer (L : Set X) :=
    Subgroup.le_centralizer_iff.mp ((le_layer_of_isComponentOf hL).trans hEC) hzO
  have hzt : z ∉ Subgroup.zpowers t := by
    intro hzt
    have hmem : (⟨z, Subgroup.zpowers_le.mpr htL hzt⟩ : L) ∈ Subgroup.center L :=
      Subgroup.mem_center_iff.mpr fun k =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC k k.2)
    rw [hZ, Subgroup.mem_bot] at hmem
    have hz1 : z = 1 := congrArg Subtype.val hmem
    rw [hz1, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hzconj : ∀ g : X, g * z * g⁻¹ ∈ Subgroup.zpowers z := fun g =>
    conj_mem_zpowers_of_isCyclic rfl hzO (‹(CFSG.pCore p X).Normal›.conj_mem z hzO g)
  have hQR : Subgroup.zpowers t ⊔ Subgroup.zpowers z ≤ R :=
    sup_le (Subgroup.zpowers_le.mpr htR)
      (Subgroup.zpowers_le.mpr (CFSG.pCore_isPGroup.le_sylow_of_normal R hzO))
  have hQ2 : 2 ≤ Open.pRank p (Subgroup.zpowers t ⊔ Subgroup.zpowers z) :=
    two_le_pRank_of_commute_of_not_mem_zpowers hp ht (hz ▸ pow_orderOf_eq_one z) hzt
      (Subgroup.mem_centralizer_iff.mp hzC t htL)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hC := h.three_le_pRank_inf_centralizer_sup_zpowers ht hz
    (fun v hv => h.conj_mem_zpowers_of_component hL hcyc ⟨htR, htL⟩ hv) fun v _ => hzconj v
  have hF : CFSG.layer X ≤ CFSG.generalizedFitting X := le_sup_right
  refine h.false_of_normalizer_inf_generalizedFitting_le (fun L' hL' => huniq L' hL' ▸ hLX₀)
    hQR hQ2 hC fun g hg => mem_normalizer_sup_zpowers ?_ (Subgroup.mem_sup_right (hzconj g))
  have hgt := (Subgroup.mem_normalizer_iff.mp hg t).mp
    ⟨htR, hF (le_layer_of_isComponentOf hL htL)⟩
  have hgtL : g * t * g⁻¹ ∈ L := huniq _
    ((ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL) ▸
      (⟨t, htL, rfl⟩ : g * t * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom)
  exact Subgroup.mem_sup_left (conj_mem_zpowers_of_isCyclic (T := (R : Subgroup X) ⊓ L) rfl
    ⟨htR, htL⟩ ⟨hgt.1, hgtL⟩)

theorem centralizer_eq_bot_of_unique_component (h : ReducedNongeneration p X R X₀)
    {L : Subgroup X} (huniq : ∀ L' : Subgroup X, IsComponentOf L' ⊤ → L' = L)
    (hZ : Subgroup.center L = ⊥) (hO : CFSG.pCore p X = ⊥) :
    Subgroup.centralizer (L : Set X) = ⊥ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hF : CFSG.generalizedFitting X ≤ L := by
    refine sup_le ?_ (sSup_le fun K hK => (huniq K ((CFSG.isComponent_iff_open K).mp hK)).le)
    rw [CFSG.Fitting_eq_pcore X p h.core_eq_bot, hO]
    exact bot_le
  have hCL : Subgroup.centralizer (L : Set X) ≤ L :=
    ((Subgroup.centralizer_le hF).trans (CFSG.centralizer_generalizedFitting_le X)).trans hF
  rw [eq_bot_iff]
  intro x hx
  have hmem : (⟨x, hCL hx⟩ : L) ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun k =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp hx k k.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)

end Frattini

section Rank

variable {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem pRank_eq_three_of_forall_isCyclic (h : ReducedNongeneration p X R X₀)
    (hX : CatalogSimpleSections X) (hKF : KFactBeta) {K : Subgroup X}
    (hK : IsComponentOf K ⊤)
    (hcyc : ∀ L : Subgroup X, IsComponentOf L ⊤ → IsCyclic ((R : Subgroup X) ⊓ L : Subgroup X)) :
    Open.pRank p (R : Subgroup X) = 3 := by
  have hp := h.prime
  have h3 := h.three_le_pRank
  suffices hle : Open.pRank p (R : Subgroup X) ≤ 3 by omega
  by_cases hex : ∃ L : Subgroup X, IsComponentOf L ⊤ ∧ ¬ L ≤ X₀
  · obtain ⟨L, hL, hLX₀⟩ := hex
    have h1 := h.pRank_inf_centralizer_le_one_of_not_le hL hLX₀
    have h2 := pRank_le_pRank_inf_centralizer_add_pRank_mulAut hp
      (h.sylow_le_normalizer_component hL)
    have h4 := h.pRank_mulAut_le_two_of_isCyclic hX hKF hL (hcyc L hL)
    omega
  push Not at hex
  exfalso
  by_cases htwo : ∃ L : Subgroup X, IsComponentOf L ⊤ ∧ L ≠ K
  · obtain ⟨L, hL, hLK⟩ := htwo
    exact h.false_of_two_components hK hL (Ne.symm hLK) hcyc hex
  push Not at htwo
  by_cases hO : CFSG.pCore p X = ⊥
  · have hC := h.centralizer_eq_bot_of_unique_component htwo
      (h.center_eq_bot_of_isCyclic hK (hcyc K hK)) hO
    have h2 := pRank_le_pRank_inf_centralizer_add_pRank_mulAut hp
      (h.sylow_le_normalizer_component hK)
    have h4 := h.pRank_mulAut_le_two_of_isCyclic hX hKF hK (hcyc K hK)
    rw [hC, inf_bot_eq, pRank_bot_eq_zero hp] at h2
    omega
  · exact h.false_of_unique_component_of_pCore_ne_bot hK htwo (hcyc K hK) (hex K hK) hO

end Rank

end ReducedNongeneration

theorem D1ComponentConfig.exists_isComponentOf {G : Type} [Group G] [Finite G] {p : ℕ}
    {P : Sylow p G} {M H R : Subgroup G} {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hcfg : D1ComponentConfig p P M H R Rbar) :
    ∃ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ := by
  obtain ⟨-, -, -, -, -, -, -, -, K, hK, -⟩ :=
    hcfg.ext.exists_reducedNongeneration_of_not_hasPrimeConstraint hcfg.glob hcfg.notCon
  exact ⟨K, hK⟩

@[expose] def D1CaseTwoRankThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p))) →
    Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = 3 → False

theorem d1CaseTwo_of_rankThree (hβ : KFactBeta) (h : D1CaseTwoRankThree) : D1CaseTwo := by
  intro G _ _ p P M H R Rbar hcfg hcyc
  obtain ⟨K, hK⟩ := hcfg.exists_isComponentOf
  exact h G p P M H R Rbar hcfg hcyc
    (hcfg.red.pRank_eq_three_of_forall_isCyclic hcfg.catalog hβ hK hcyc)

end CFSG.AGLEmbedding
