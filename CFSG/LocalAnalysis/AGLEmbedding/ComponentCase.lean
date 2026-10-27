module

public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent
public import CFSG.LocalAnalysis.AGLEmbedding.Obligations

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

theorem CatalogSimpleSections.isCatalogGroup_center_quotient {X : Type*} [Group X]
    (hX : CatalogSimpleSections X) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    IsCatalogGroup (K ⧸ Subgroup.center K) :=
  hX K (Subgroup.center K) inferInstance hK.2.2.2
    (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2)

namespace ReducedNongeneration

variable {p : ℕ} {X : Type*} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem rankOne_or_center (h : ReducedNongeneration p X R X₀) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hnc : ¬ IsCyclic ((R : Subgroup X) ⊓ K : Subgroup X)) :
    (∃ z ∈ (R : Subgroup X), z ∉ K ∧ orderOf z = p ∧ z ∈ Subgroup.centralizer (K : Set X) ∧
      (∀ U : Subgroup X, U ≤ (R : Subgroup X) ⊓ K → U ≠ ⊥ →
        K ⊓ Subgroup.normalizer (U : Set X) ≤ X₀) ∧ ¬ K ≤ X₀ ∧
      Subgroup.normalizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) ≤ X₀ ∧
      Subgroup.center K = ⊥) ∨
    ∀ z ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), orderOf z = p →
      z ∈ (Subgroup.center K).map K.subtype := by
  by_cases hz : ∃ z ∈ (R : Subgroup X), z ∉ K ∧ orderOf z = p ∧
      z ∈ Subgroup.centralizer (K : Set X)
  · obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hz
    obtain ⟨hN, hK₀⟩ := h.rankOne_principle hK hnc hzR hzK hzp hzc
    exact Or.inl ⟨z, hzR, hzK, hzp, hzc, hN, hK₀,
      h.normalizer_inf_le_of_rankOne hnc hzR hzK hzp hzc,
      h.center_eq_bot_of_rankOne hK hnc hzR hzK hzp hzc⟩
  · refine Or.inr fun z ⟨hzR, hzc⟩ hzp => ?_
    have hzK : z ∈ K := by
      by_contra hzK
      exact hz ⟨z, hzR, hzK, hzp, hzc⟩
    exact ⟨⟨z, hzK⟩, Subgroup.mem_center_iff.mpr fun k =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hzc k k.2), rfl⟩

end ReducedNongeneration

theorem D1Escape.ne_top {G : Type*} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M H R : Subgroup G} (h : D1Escape p P M H R) : H ≠ ⊤ := fun htop =>
  h.not_le (h.maxTwoLocal_M.2 H h.maxTwoLocal_H.1 (htop ▸ le_top)).le

theorem D1Escape.exists_reducedNongeneration_of_not_hasPrimeConstraint {G : Type} [Group G]
    [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} (hK : Open.IsKProper G)
    {H R : Subgroup G} (h : D1Escape p P M H R) (hcon : ¬ HasPrimeConstraint (G := H) p) :
    ∃ Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) ∧
      ReducedNongeneration p (H ⧸ primeComplementCore (G := H) p) Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) ∧
      CatalogSimpleSections (H ⧸ primeComplementCore (G := H) p) ∧
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
        (Rbar : Subgroup _) ≤
          Subgroup.normalizer (L : Set (H ⧸ primeComplementCore (G := H) p)) ∧
        IsCatalogGroup (L ⧸ Subgroup.center L) ∧ p ∣ Nat.card (L ⧸ Subgroup.center L)) ∧
      (∀ L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
        IsComponentOf L₂ ⊤ → 2 ≤ Open.pRank p ((Rbar : Subgroup _) ⊓ L₁) →
        2 ≤ Open.pRank p ((Rbar : Subgroup _) ⊓ L₂) → L₁ = L₂) ∧
      (∀ L₁ L₂ L₃ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
        IsComponentOf L₂ ⊤ → IsComponentOf L₃ ⊤ → L₁ ≠ L₂ → L₁ ≠ L₃ → L₂ ≠ L₃ → False) ∧
      IsCyclic (CFSG.pCore p (H ⧸ primeComplementCore (G := H) p)) ∧
      ∃ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ ∧
        IsCatalogGroup (K ⧸ Subgroup.center K) ∧ p ∣ Nat.card (K ⧸ Subgroup.center K) := by
  have hp := h.prime
  obtain ⟨Rbar, hRbar, hred⟩ := h.reducedNongeneration
  have hX : CatalogSimpleSections (H ⧸ primeComplementCore (G := H) p) :=
    (catalogSimpleSections_of_isKProper hK H h.ne_top).quotient _
  obtain ⟨K, hK, -, -, -, hKp, hKcat⟩ :=
    isKProper_not_hasPrimeConstraint_catalog_component hK H h.ne_top p hp hcon
  exact ⟨Rbar, hRbar, hred, hX, fun L hL => ⟨hred.sylow_le_normalizer_component hL,
      hX.isCatalogGroup_center_quotient hL,
      prime_dvd_card_center_quotient_of_isComponentOf hp hred.core_eq_bot hL⟩,
    fun _ _ h₁ h₂ hr₁ hr₂ => hred.eq_of_two_le_pRank h₁ h₂ hr₁ hr₂,
    fun _ _ _ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ => hred.false_of_three_components h₁ h₂ h₃ h₁₂ h₁₃ h₂₃,
    hred.isCyclic_pCore_of_component hK, K, hK, hKcat, hKp⟩

theorem D1Extremal.exists_reducedNongeneration_of_not_hasPrimeConstraint {G : Type} [Group G]
    [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} (hglob : D1Global G)
    {H R : Subgroup G} (h : D1Extremal p P M H R) (hcon : ¬ HasPrimeConstraint (G := H) p) :
    ∃ Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p),
      (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) ∧
      ReducedNongeneration p (H ⧸ primeComplementCore (G := H) p) Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) ∧
      CatalogSimpleSections (H ⧸ primeComplementCore (G := H) p) ∧
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
        (Rbar : Subgroup _) ≤
          Subgroup.normalizer (L : Set (H ⧸ primeComplementCore (G := H) p)) ∧
        IsCatalogGroup (L ⧸ Subgroup.center L) ∧ p ∣ Nat.card (L ⧸ Subgroup.center L)) ∧
      (∀ L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
        IsComponentOf L₂ ⊤ → 2 ≤ Open.pRank p ((Rbar : Subgroup _) ⊓ L₁) →
        2 ≤ Open.pRank p ((Rbar : Subgroup _) ⊓ L₂) → L₁ = L₂) ∧
      (∀ L₁ L₂ L₃ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
        IsComponentOf L₂ ⊤ → IsComponentOf L₃ ⊤ → L₁ ≠ L₂ → L₁ ≠ L₃ → L₂ ≠ L₃ → False) ∧
      IsCyclic (CFSG.pCore p (H ⧸ primeComplementCore (G := H) p)) ∧
      ∃ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ ∧
        IsCatalogGroup (K ⧸ Subgroup.center K) ∧ p ∣ Nat.card (K ⧸ Subgroup.center K) :=
  h.toD1Escape.exists_reducedNongeneration_of_not_hasPrimeConstraint hglob.kProper hcon

@[expose] def D1ReducedComponentCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D1Global G →
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), D1Local p P M →
      ∀ H R : Subgroup G, D1Extremal p P M H R → ¬ HasPrimeConstraint (G := H) p →
      ∀ Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p),
        (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
        ReducedNongeneration p (H ⧸ primeComplementCore (G := H) p) Rbar
          (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) →
        CatalogSimpleSections (H ⧸ primeComplementCore (G := H) p) →
        (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
          (Rbar : Subgroup _) ≤
            Subgroup.normalizer (L : Set (H ⧸ primeComplementCore (G := H) p)) ∧
          IsCatalogGroup (L ⧸ Subgroup.center L) ∧ p ∣ Nat.card (L ⧸ Subgroup.center L)) →
        (∀ L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
          IsComponentOf L₂ ⊤ → 2 ≤ Open.pRank p ((Rbar : Subgroup _) ⊓ L₁) →
          2 ≤ Open.pRank p ((Rbar : Subgroup _) ⊓ L₂) → L₁ = L₂) →
        (∀ L₁ L₂ L₃ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
          IsComponentOf L₂ ⊤ → IsComponentOf L₃ ⊤ → L₁ ≠ L₂ → L₁ ≠ L₃ → L₂ ≠ L₃ → False) →
        IsCyclic (CFSG.pCore p (H ⧸ primeComplementCore (G := H) p)) →
        ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
          IsCatalogGroup (K ⧸ Subgroup.center K) → p ∣ Nat.card (K ⧸ Subgroup.center K) → False

theorem d1ComponentCase_of_reducedComponentCase (h : D1ReducedComponentCase) :
    D1ComponentCase := by
  intro G _ _ hglob p P M hloc H R hext hcon
  obtain ⟨Rbar, hRbar, hred, hX, hL, h2, h3, hcyc, K, hK, hKcat, hKp⟩ :=
    hext.exists_reducedNongeneration_of_not_hasPrimeConstraint hglob hcon
  exact h G hglob p P M hloc H R hext hcon Rbar hRbar hred hX hL h2 h3 hcyc K hK hKcat hKp

end CFSG.AGLEmbedding
