module

public import CFSG.LocalAnalysis.AGLEmbedding.Induction

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

theorem pRank_le_pRank_inf_centralizer_add_pRank_mulAut {X : Type*} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) {K R : Subgroup X} (hR : R ≤ Subgroup.normalizer (K : Set X)) :
    Open.pRank p R ≤ Open.pRank p (R ⊓ Subgroup.centralizer (K : Set X)) +
      Open.pRank p (⊤ : Subgroup (MulAut K)) := by
  set N := Subgroup.normalizer (K : Set X)
  have hineq := pRank_le_pRank_inf_ker_add_pRank_map hp K.normalizerMonoidHom (R.subgroupOf N)
  have h₁ : Open.pRank p (R.subgroupOf N) = Open.pRank p R := by
    rw [← pRank_map_of_injective p hp N.subtype N.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hR]
  have h₂ : Open.pRank p (R.subgroupOf N ⊓ K.normalizerMonoidHom.ker) ≤
      Open.pRank p (R ⊓ Subgroup.centralizer (K : Set X)) := by
    rw [Subgroup.normalizerMonoidHom_ker,
      ← pRank_map_of_injective p hp N.subtype N.subtype_injective]
    refine pRank_mono p hp ?_
    rintro _ ⟨x, ⟨hxR, hxC⟩, rfl⟩
    exact ⟨hxR, hxC⟩
  have h₃ := pRank_mono p hp (le_top : (R.subgroupOf N).map K.normalizerMonoidHom ≤ ⊤)
  omega

namespace ReducedNongeneration

section Rank

variable {p : ℕ} {X : Type*} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem pRank_inf_centralizer_le_one_of_not_le (h : ReducedNongeneration p X R X₀)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) (hKX₀ : ¬ K ≤ X₀) :
    Open.pRank p ((R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X)) ≤ 1 := by
  have hp := h.prime
  by_contra! h₂
  obtain ⟨F, hF, hFel, hFcard⟩ := exists_isElemAbelian_card_sq_of_two_le_pRank hp h₂
  obtain ⟨t, ⟨htR, htK⟩, ht, htC⟩ :=
    exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R hK
  have hFC : F ≤ Subgroup.centralizer (K : Set X) := hF.trans inf_le_right
  have hN := h.normalizer_le_of_mem_centralizer htR (fun htF => htC (hFC htF)) ht
    (Subgroup.le_centralizer_iff.mp hFC htK) (hF.trans inf_le_left)
    (le_csSup (pRank_bddAbove p hp F) ⟨F, le_rfl, hFel, hFcard⟩)
  exact hKX₀ ((Subgroup.le_centralizer_iff.mp hFC).trans
    ((Subgroup.centralizer_le_normalizer _).trans hN))

theorem pRank_eq_three_of_pRank_mulAut_le_two (h : ReducedNongeneration p X R X₀)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) (hKX₀ : ¬ K ≤ X₀)
    (hAut : Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2) :
    Open.pRank p (R : Subgroup X) = 3 := by
  have h₁ := h.pRank_inf_centralizer_le_one_of_not_le hK hKX₀
  have hineq := pRank_le_pRank_inf_centralizer_add_pRank_mulAut h.prime
    (h.sylow_le_normalizer_component hK)
  have h₃ := h.three_le_pRank
  omega

theorem eq_of_forall_mem_center (h : ReducedNongeneration p X R X₀) {K L : Subgroup X}
    (hK : IsComponentOf K ⊤) (hL : IsComponentOf L ⊤)
    (hcent : ∀ c ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype) : L = K := by
  by_contra hLK
  obtain ⟨t, ⟨htR, htL⟩, ht, htC⟩ :=
    exists_mem_sylow_inf_component h.prime h.ne_two h.core_eq_bot R hL
  have htK : t ∈ K := Subgroup.map_subtype_le _
    (hcent t ⟨htR, le_centralizer_of_component_ne hL hK hLK htL⟩ ht)
  exact htC (le_centralizer_of_component_ne hK hL (Ne.symm hLK) htK)

end Rank

section KFact

variable {p : ℕ} {X : Type} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem pRank_mulAut_le_two_or_rankOneLieAutFacts (h : ReducedNongeneration p X R X₀)
    (hX : CatalogSimpleSections X) (hKF : KFactBeta) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hZ : Subgroup.center K = ⊥)
    (hN : ∀ U : Subgroup X, U ≤ (R : Subgroup X) ⊓ K → U ≠ ⊥ →
      K ⊓ Subgroup.normalizer (U : Set X) ≤ X₀) (hKX₀ : ¬ K ≤ X₀) :
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 ∨ RankOneLieAutFacts p K := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  let e : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.2.2
  have hsimple : IsSimpleGroup K := e.isSimpleGroup
  have hnonab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2
    refine ⟨e.symm a, e.symm b, fun hba => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e hba
  have hcat : IsCatalogGroup K :=
    IsCatalogGroup.of_mulEquiv e (hX.isCatalogGroup_center_quotient hK)
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R
    (ComponentClassification.Components.mathlib_subnormal_of_chain hK.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨t, htRK, ht, -⟩ := exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot R hK
  have hTne : (T : Subgroup K) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.map_bot] at hT
    have ht1 : t ∈ (⊥ : Subgroup X) := by
      rw [hT]
      exact htRK
    rw [Subgroup.mem_bot] at ht1
    rw [ht1, orderOf_one] at ht
    exact hp.one_lt.ne ht
  exact hKF K hsimple hnonab hcat p hp h.ne_two T hTne
    (Or.inr (h.glbCore_ne_top_of_rankOne hN hKX₀ hT))

end KFact

end ReducedNongeneration

structure D1ComponentConfig {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G)
    (M H R : Subgroup G) (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)) : Prop where
  glob : D1Global G
  loc : D1Local p P M
  ext : D1Extremal p P M H R
  notCon : ¬ HasPrimeConstraint (G := H) p
  ind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q
  rbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))
  red : ReducedNongeneration p (H ⧸ primeComplementCore (G := H) p) Rbar
    (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
  catalog : CatalogSimpleSections (H ⧸ primeComplementCore (G := H) p)

@[expose] def D1CaseOneSmall : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      Subgroup.center K = ⊥ →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∃ z ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)), z ∉ K ∧ orderOf z = p ∧
        z ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))) →
      Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 →
      Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = 3 → False

@[expose] def D1CaseOneLie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      Subgroup.center K = ⊥ →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∃ z ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)), z ∉ K ∧ orderOf z = p ∧
        z ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))) →
      RankOneLieAutFacts p K → False

@[expose] def D1CaseTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p))) → False

@[expose] def D1CaseThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) → False

theorem D1Extremal.exists_componentConfig {G : Type} [Group G] [Finite G] {p : ℕ}
    {P : Sylow p G} {M H R : Subgroup G} (hglob : D1Global G) (hloc : D1Local p P M)
    (hext : D1Extremal p P M H R) (hcon : ¬ HasPrimeConstraint (G := H) p)
    (hind : ∀ q ∈ GLBBetaFour G, q < p → D1At G q) :
    ∃ Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p),
      D1ComponentConfig p P M H R Rbar := by
  obtain ⟨Rbar, hRbar, hred, hX, -⟩ :=
    hext.exists_reducedNongeneration_of_not_hasPrimeConstraint hglob hcon
  exact ⟨Rbar, hglob, hloc, hext, hcon, hind, hRbar, hred, hX⟩

theorem d1ComponentCaseInd_of_cases (hβ : KFactBeta) (h1s : D1CaseOneSmall)
    (h1l : D1CaseOneLie) (h2 : D1CaseTwo) (h3 : D1CaseThree) : D1ComponentCaseInd := by
  intro G _ _ hglob p hind P M hloc H R hext hcon
  obtain ⟨Rbar, hcfg⟩ := hext.exists_componentConfig hglob hloc hcon hind
  have hred := hcfg.red
  by_cases hall : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p))
  · exact h2 G p P M H R Rbar hcfg hall
  push Not at hall
  obtain ⟨K, hK, hnc⟩ := hall
  rcases hred.rankOne_or_center hK hnc with ⟨z, hzR, hzK, hzp, hzc, hN, hKX₀, -, hZ⟩ | hcent
  · rcases hred.pRank_mulAut_le_two_or_rankOneLieAutFacts hcfg.catalog hβ hK hZ hN hKX₀ with
      hAut | hfacts
    · exact h1s G p P M H R Rbar hcfg K hK hZ hnc ⟨z, hzR, hzK, hzp, hzc⟩ hAut
        (hred.pRank_eq_three_of_pRank_mulAut_le_two hK hKX₀ hAut)
    · exact h1l G p P M H R Rbar hcfg K hK hZ hnc ⟨z, hzR, hzK, hzp, hzc⟩ hfacts
  · exact h3 G p P M H R Rbar hcfg K hK (fun L hL => hred.eq_of_forall_mem_center hK hL hcent)
      hnc hcent

end CFSG.AGLEmbedding
