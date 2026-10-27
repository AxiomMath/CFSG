module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Constrained3
public import CFSG.LocalAnalysis.AGLEmbedding.KlingenRoute
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactSections3
import CFSG.LocalAnalysis.AGLEmbedding.NoXBlockBridgeK
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Cases3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.Assembly.LowTwoRank
open CFSG.AGLEmbedding (D1Extremal D1Escape ReducedNongeneration CatalogSimpleSections
  RankOneLieAutFacts HasKlingenData InClassXBlock succ_le_pRank_of_isElemAbelian_of_mem_centralizer
  catalogSimpleSections_of_isKProper isKProper_not_hasPrimeConstraint_catalog_component
  pRank_map_mk_eq_pRank_map_subtype exists_lift_of_le_map isElemAbelian_of_mulEquiv
  pow_eq_one_of_mulEquiv
  exists_mem_normalizer_mk_eq_of_mem_normalizer exists_mem_normalizer_mk_eq_commute
  exists_mem_center_of_normalizer_not_le pRank_inf_centralizer_le_two_of_normalizer_not_le
  orderOf_mk_of_coprime statedSL_le_map_centerQuotientAction_of_mulEquiv)

variable {G : Type} [Group G] [Finite G]

structure D1Local3 {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) :
    Prop where
  sigma : p ∈ rankThreeSigmaA G
  maxLocal : GLBIsMaxTwoLocal M
  core : GLBWeakCore p (P : Subgroup G) ≤ M

namespace D1Local3

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem ne_two (h : D1Local3 p P M) : p ≠ 2 := sigmaA_odd p h.sigma

theorem isCoreMaxLocal (h : D1Local3 p P M) : IsCoreMaxLocal p P M := ⟨h.maxLocal, h.core⟩

end D1Local3

theorem exists_reducedNongeneration_of_not_hasPrimeConstraint3 {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} (hK : Open.IsKProper G) (h : D1Extremal p P M H R)
    (hcon : ¬ HasPrimeConstraint (G := H) p) :
    ∃ Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) ∧
      ReducedNongeneration p (H ⧸ primeComplementCore (G := H) p) Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) ∧
      CatalogSimpleSections (H ⧸ primeComplementCore (G := H) p) ∧
      ∃ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ ∧
        IsCatalogGroup (K ⧸ Subgroup.center K) ∧ p ∣ Nat.card (K ⧸ Subgroup.center K) := by
  obtain ⟨Rbar, hRbar, hred⟩ := h.reducedNongeneration
  obtain ⟨K, hKc, -, -, -, hKp, hKcat⟩ :=
    isKProper_not_hasPrimeConstraint_catalog_component hK H h.ne_top p h.prime hcon
  exact ⟨Rbar, hRbar, hred, (catalogSimpleSections_of_isKProper hK H h.ne_top).quotient _, K, hKc,
    hKcat, hKp⟩

structure D1ComponentConfig3 {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G)
    (M H R : Subgroup G) (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)) : Prop where
  glob : Setting G
  loc : D1Local3 p P M
  ext : D1Extremal p P M H R
  notCon : ¬ HasPrimeConstraint (G := H) p
  ind : ∀ q ∈ rankThreeSigmaA G, q < p → D1At3 G q
  rbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))
  red : ReducedNongeneration p (H ⧸ primeComplementCore (G := H) p) Rbar
    (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
  catalog : CatalogSimpleSections (H ⧸ primeComplementCore (G := H) p)

theorem exists_componentConfig3 (hS : Setting G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M H R : Subgroup G} (hM : IsCoreMaxLocal p P M)
    (hext : D1Extremal p P M H R) (hcon : ¬ HasPrimeConstraint (G := H) p)
    (hind : ∀ q ∈ rankThreeSigmaA G, q < p → D1At3 G q) :
    ∃ Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p),
      D1ComponentConfig3 p P M H R Rbar := by
  obtain ⟨Rbar, hRbar, hred, hX, -⟩ :=
    exists_reducedNongeneration_of_not_hasPrimeConstraint3 hS.kProper hext hcon
  exact ⟨Rbar, hS, ⟨hp, hM.1, hM.2⟩, hext, hcon, hind, hRbar, hred, hX⟩

namespace D1ComponentConfig3

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem exists_isComponentOf (h : D1ComponentConfig3 p P M H R Rbar) :
    ∃ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ := by
  obtain ⟨-, -, -, -, K, hK, -⟩ :=
    exists_reducedNongeneration_of_not_hasPrimeConstraint3 h.glob.kProper h.ext h.notCon
  exact ⟨K, hK⟩

theorem pRank_eq_three (h : D1ComponentConfig3 p P M H R Rbar) :
    Open.pRank p (P : Subgroup G) = 3 :=
  (sylow_le_of_isCoreMaxLocal h.glob h.loc.sigma h.loc.isCoreMaxLocal).2

theorem pRank_rbar_eq_three (h : D1ComponentConfig3 p P M H R Rbar) :
    Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = 3 := by
  have hp := h.ext.prime
  have h3 := h.red.three_le_pRank
  have hle : Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤ 3 := by
    rw [h.rbar, pRank_map_mk_eq_pRank_map_subtype hp _ (primeComplementCore_coprime p),
      Subgroup.map_subgroupOf_eq_of_le h.ext.le_H]
    exact (PreuniquenessRankFour.Helpers.pRank_mono p hp h.ext.le_P).trans h.pRank_eq_three.le
  omega

end D1ComponentConfig3

@[expose] def D1CaseOneSmall3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      Subgroup.center K = ⊥ →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∃ z ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)), z ∉ K ∧ orderOf z = p ∧
        z ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))) →
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 →
      Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = 3 → False

@[expose] def D1CaseTwo3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p))) → False

@[expose] def D1CaseThree3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) → False

theorem pRank_mulAut_le_two_of_component3 {X : Type} [Group X] [Finite X]
    (hX : CatalogSimpleSections X) (hKF : KFactBetaRank2) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hZ : Subgroup.center K = ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (T : Sylow p K) (hTne : (T : Subgroup K) ≠ ⊥) (hrk : Open.pRank p (T : Subgroup K) ≤ 2)
    (hcond : IsCyclic (T : Subgroup K) ∨ GLBCore p 1 (T : Subgroup K) ≠ ⊤) :
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  let e : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  have hnonab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2
    refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba
  exact hKF K e.isSimpleGroup hnonab
    (CFSG.AGLEmbedding.IsCatalogGroup.of_mulEquiv e (hX.isCatalogGroup_center_quotient hK))
    p hp hp2 T hTne hrk hcond

theorem pRank_inf_succ_le_of_central {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X]
    {R K : Subgroup X} {z : X} (hzR : z ∈ R) (hzp : orderOf z = p) (hzK : z ∉ K)
    (hzc : z ∈ Subgroup.centralizer (K : Set X)) :
    Open.pRank p (R ⊓ K) + 1 ≤ Open.pRank p R := by
  obtain ⟨E, hE, hEel, hEcard⟩ := pRank_attained p hp (R ⊓ K)
  refine succ_le_pRank_of_isElemAbelian_of_mem_centralizer hp hEel hEcard
    (hzp ▸ pow_orderOf_eq_one z) (fun hzE => hzK (hE hzE).2) ?_ (hE.trans inf_le_left) hzR
  exact Subgroup.mem_centralizer_iff.mpr fun e he =>
    Subgroup.mem_centralizer_iff.mp hzc e (hE he).2

theorem pRank_sylow_component_le_two {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X]
    {R : Subgroup X} {K : Subgroup X} (T : Subgroup K)
    (hT : T.map K.subtype = R ⊓ K) {z : X} (hzR : z ∈ R) (hzp : orderOf z = p) (hzK : z ∉ K)
    (hzc : z ∈ Subgroup.centralizer (K : Set X)) (hR3 : Open.pRank p R ≤ 3) :
    Open.pRank p T ≤ 2 := by
  have := pRank_inf_succ_le_of_central hp hzR hzp hzK hzc
  rw [← hT, pRank_map_of_injective p hp K.subtype K.subtype_injective] at this
  omega

theorem exists_sylow_ne_bot_map_eq_inf_of_component3 {p : ℕ} {X : Type} [Group X] [Finite X]
    {R : Sylow p X} {X₀ : Subgroup X} (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) :
    ∃ T : Sylow p K, (T : Subgroup K) ≠ ⊥ ∧
      (T : Subgroup K).map K.subtype = (R : Subgroup X) ⊓ K := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R
    (CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨t, htRK, ht, -⟩ :=
    CFSG.AGLEmbedding.exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R hK
  refine ⟨T, fun hbot => ?_, hT⟩
  rw [hbot, Subgroup.map_bot] at hT
  have ht1 : t ∈ (⊥ : Subgroup X) := by
    rw [hT]
    exact htRK
  rw [Subgroup.mem_bot] at ht1
  rw [ht1, orderOf_one] at ht
  exact hp.one_lt.ne ht

theorem pRank_mulAut_le_two3 {p : ℕ} {X : Type} [Group X] [Finite X]
    {R : Sylow p X} {X₀ : Subgroup X} (h : ReducedNongeneration p X R X₀)
    (hR3 : Open.pRank p (R : Subgroup X) ≤ 3)
    (hX : CatalogSimpleSections X) (hKF : KFactBetaRank2) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hZ : Subgroup.center K = ⊥)
    {z : X} (hzR : z ∈ (R : Subgroup X)) (hzp : orderOf z = p) (hzK : z ∉ K)
    (hzc : z ∈ Subgroup.centralizer (K : Set X))
    (hN : ∀ U : Subgroup X, U ≤ (R : Subgroup X) ⊓ K → U ≠ ⊥ →
      K ⊓ Subgroup.normalizer (U : Set X) ≤ X₀) (hKX₀ : ¬ K ≤ X₀) :
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  obtain ⟨T, hTne, hT⟩ := exists_sylow_ne_bot_map_eq_inf_of_component3 h hK
  exact pRank_mulAut_le_two_of_component3 hX hKF hK hZ h.prime h.ne_two T hTne
    (pRank_sylow_component_le_two h.prime (T : Subgroup K) hT hzR hzp hzK hzc hR3)
    (Or.inr (h.glbCore_ne_top_of_rankOne hN hKX₀ hT))

theorem d1ComponentCaseInd3_of_cases (hK3 : KFactsA3 G) (h1s : D1CaseOneSmall3 G)
    (h2 : D1CaseTwo3 G) (h3 : D1CaseThree3 G) : D1ComponentCaseInd3 G := by
  intro hS p hp hind P M hM H R hext hcon
  obtain ⟨Rbar, hcfg⟩ := exists_componentConfig3 hS hp hM hext hcon hind
  have hred := hcfg.red
  by_cases hall : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p))
  · exact h2 p P M H R Rbar hcfg hall
  push Not at hall
  obtain ⟨K, hK, hnc⟩ := hall
  rcases hred.rankOne_or_center hK hnc with ⟨z, hzR, hzK, hzp, hzc, hN, hKX₀, -, hZ⟩ | hcent
  · have hAut := pRank_mulAut_le_two3 hred hcfg.pRank_rbar_eq_three.le hcfg.catalog hK3.beta hK hZ
      hzR hzp hzK hzc hN hKX₀
    exact h1s p P M H R Rbar hcfg K hK hZ hnc ⟨z, hzR, hzK, hzp, hzc⟩ hAut
      (hred.pRank_eq_three_of_pRank_mulAut_le_two hK hKX₀ hAut)
  · exact h3 p P M H R Rbar hcfg K hK (fun L hL => hred.eq_of_forall_mem_center hK hL hcent)
      hnc hcent

@[expose] def D1CaseThreeNotKlingen3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ¬ HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) → False

@[expose] def D1NoXBlock3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → ∀ M Y : Subgroup G, GLBIsMaxTwoLocal M → Y ≤ M → Open.IsSubnormal Y M →
    InClassXBlock Y → False

theorem d1NoXBlock3_of_inputsK (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK) : D1NoXBlock3 G := by
  intro hS M Y hM hYM hsub hY
  have hrank : 3 ≤ CFSG.Assembly.evenRank G :=
    (CFSG.AGLEmbedding.NoXBlock.open_evenRank_eq (G := G)) ▸ hS.rank.ge
  have hle := CFSG.AGLEmbedding.NoXBlock.evenRank_le_two_of_inOmegaK h1 h2 h25
    (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.mp hS.kProper) hS.simple
    (CFSG.AGLEmbedding.NoXBlock.assembly_isCharTwoType_of_open hS.charTwo)
    ⟨CFSG.AGLEmbedding.NoXBlock.inClassX_of_inClassXBlock hY, M,
      CFSG.AGLEmbedding.NoXBlock.isMaximalTwoLocal_of_glb hM, hYM,
      CFSG.AGLEmbedding.NoXBlock.isSubnormal_subgroupOf_of_open hsub⟩
  omega

theorem false_of_extremal_of_theoremD1 (hD1 : TheoremD1 G) (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M H R : Subgroup G}
    (hM : IsCoreMaxLocal p P M) (h : D1Extremal p P M H R) : False :=
  d1ExtremalCase3_of_theoremD1 hD1 hS p hp P M hM H R h

theorem residues3_of_theoremD1 (hD1 : TheoremD1 G) :
    D1CentralizerSylowCase3 G ∧ D1CentralizerComponentCase3 G ∧
      D1CentralizerConstrainedCase3 G ∧ D1CaseOneSmall3 G ∧ D1CaseTwo3 G ∧
      D1CaseThreeNotKlingen3 G := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hS p hp P M hM H R hext
    exact (false_of_extremal_of_theoremD1 hD1 hS hp hM hext).elim
  · intro hS p hp P M hM H R hext
    exact (false_of_extremal_of_theoremD1 hD1 hS hp hM hext).elim
  · intro hS p hp P M hM H R hext
    exact (false_of_extremal_of_theoremD1 hD1 hS hp hM hext).elim
  · intro p P M H R Rbar hcfg
    exact (false_of_extremal_of_theoremD1 hD1 hcfg.glob hcfg.loc.sigma hcfg.loc.isCoreMaxLocal
      hcfg.ext).elim
  · intro p P M H R Rbar hcfg
    exact (false_of_extremal_of_theoremD1 hD1 hcfg.glob hcfg.loc.sigma hcfg.loc.isCoreMaxLocal
      hcfg.ext).elim
  · intro p _ P M H R Rbar hcfg
    exact (false_of_extremal_of_theoremD1 hD1 hcfg.glob hcfg.loc.sigma hcfg.loc.isCoreMaxLocal
      hcfg.ext).elim

end CFSG.LocalAnalysis.RankThreeTheoremC
