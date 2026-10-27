module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoRank
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def IsCaseTwoIndex (p : ℕ) (d : TauCeti.ValidLieTypeIndex) : Prop :=
  (p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .A 1 q) ∨
    (p = 5 ∧ d.1 = .suzuki 2)

@[expose] def IsCaseTwoGroup (p : ℕ) (L : Type) [Group L] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, IsCaseTwoIndex p d ∧
    Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group)

section Defs

variable {G : Type} [Group G] [Finite G]

structure D1CaseTwoData (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)) : Prop where
  cfg : D1ComponentConfig p P M H R Rbar
  cyclic : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
    IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
      Subgroup (H ⧸ primeComplementCore (G := H) p))
  rank : Open.pRank p (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = 3

@[expose] def d1LayerX (p : ℕ) (H R : Subgroup G) : Subgroup G :=
  d1LiftX p H R (CFSG.layer (H ⧸ primeComplementCore (G := H) p))

@[expose] def D1CaseTwoClass (p : ℕ) (P : Sylow p G) (M R X H : Subgroup G) : Prop :=
  ∃ Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p),
    D1CaseTwoData p P M H R Rbar ∧ d1LayerX p H R = X

abbrev d1X0 (p : ℕ) (M H : Subgroup G) : Subgroup (H ⧸ primeComplementCore (G := H) p) :=
  ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))

end Defs

@[expose] def KFactSeitzCyc : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K, (T : Subgroup K) ≠ ⊥ →
      IsCyclic (T : Subgroup K) → ∀ E : Subgroup (MulAut K), IsElemAbelian p E →
        Nat.card E = p ^ 2 → ¬ E ≤ (MulAut.conj : K →* MulAut K).range →
        Subgroup.closure {k : K | ∃ e ∈ E, e ≠ 1 ∧ e k = k} ≠ ⊤ → IsCaseTwoGroup p K

@[expose] def KFactCaseTwoLocal : Prop :=
  ∀ (p : ℕ) (K : Type) [Group K] [Finite K], IsCaseTwoGroup p K →
    KFactUPrime p K ∧
    (∀ t : K, orderOf t = p → IsPGroup p (MulAction.stabilizer (MulAut K) t)) ∧
    ∀ T : Sylow p K,
      (∃ s ∈ Subgroup.normalizer ((T : Subgroup K) : Set K),
        ∀ x ∈ (T : Subgroup K), s * x * s⁻¹ = x → x = 1) ∧
      (∀ f : MulAut K, (∀ x ∈ (T : Subgroup K), f x = x) →
        ∃ t ∈ (T : Subgroup K), f = MulAut.conj t) ∧
      Group.IsSolvable (GLBCore p 1 (T : Subgroup K))

@[expose] def KFactCaseTwoInv : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, (p = 3 ∨ p = 5) → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      Open.pRank p (⊤ : Subgroup K) ≤ 2 →
      ∀ (A : Subgroup K) (L : Type) [Group L], IsCaseTwoGroup p L →
        ∀ f : A →* L, ¬ Function.Surjective f

@[expose] def KFactCaseTwoCM : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, (p = 3 ∨ p = 5) → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      3 ≤ Open.pRank p (⊤ : Subgroup (MulAut K)) →
      ∀ (A : Subgroup K) (L : Type) [Group L], IsCaseTwoGroup p L →
        ∀ f : A →* L, Function.Surjective f →
        p = 3 ∧ ∀ (B : Subgroup K) (Y : Type) [Group Y] (g : B →* Y), Function.Surjective g →
          IsSimpleGroup Y → (∃ a b : Y, a * b ≠ b * a) →
          (IsClassicalTwoOrG2 Y ∨ IsOrthogonalTwo Y ∨
            ∃ n : ℕ, Nonempty (Y ≃* alternatingGroup (Fin n))) →
          IsCaseTwoGroup 3 Y ∧ ¬ IsOrthogonalTwo Y ∧
            ¬ ∃ n : ℕ, Nonempty (Y ≃* alternatingGroup (Fin n))

@[expose] def KFactCaseTwoAlphaElim : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K →
    IsCatalogGroup (K ⧸ Subgroup.center K) → ∀ p : ℕ, (p = 3 ∨ p = 5) →
    Subgroup.center K ≠ ⊥ → IsPGroup p (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    ∀ (A : Subgroup K) (L : Type) [Group L], IsCaseTwoGroup p L →
      ∀ f : A →* L, Function.Surjective f → ∀ T : Sylow p K,
        (KGenThree p K ∧ (3 ≤ Open.pRank p (⊤ : Subgroup K) ∨ KOutNormalSylow p K)) ∨
        Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 ∨
        (GLBWeakCore p (T : Subgroup K) = ⊤ ∧ 3 ≤ Open.pRank p (⊤ : Subgroup K))

@[expose] def KFactCatalogSchreier : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → Group.IsSolvable (Outer K)

@[expose] def KFactL28Parabolic : Prop :=
  ∀ (Λ : Type) [Group Λ] [Finite Λ], Open.IsQuasisimple Λ →
    IsCaseTwoGroup 3 (Λ ⧸ Subgroup.center Λ) →
    Subgroup.center Λ = ⊥ ∧ ∀ T J : Subgroup Λ, IsSylowTwoOf T ⊤ →
      Subgroup.normalizer (T : Set Λ) ≤ J → J ≠ ⊤ → pCoreOf 2 J = T

@[expose] def D1CaseTwoPosZero : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
    D1UniqueOver H R (nclIn H (d1LayerX p H R)) → pCorePreimage p M ⊓ R = ⊥ → False

@[expose] def D1CaseTwoPosNTwoA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
    D1UniqueOver H R (nclIn H (d1LayerX p H R)) →
    ∀ L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
      IsComponentOf L₂ ⊤ → ¬ L₁ ≤ d1X0 p M H → L₂ ≤ d1X0 p M H →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥ →
      False

@[expose] def D1CaseTwoZZ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
    D1UniqueOver H R (nclIn H (d1LayerX p H R)) →
    ∀ L₁ : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L₁ ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = L₁) →
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L₁) ≠ ⊥ →
      d1MapPCore p M H ⊓ CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) = ⊥ →
      ¬ IsPGroup p (Subgroup.centralizer (L₁ : Set (H ⧸ primeComplementCore (G := H) p))) →
      ∀ z : H, (z : G) ∈ R → orderOf z = p →
        QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
          CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) →
        (z : G) ∈ nclIn M ⁅GLBPrimeCore p H, nclIn H (d1LayerX p H R)⁆ → False

@[expose] def D1CaseTwoZZThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M H R : Subgroup G)
    (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)), D1CaseTwoData 3 P M H R Rbar →
    D1UniqueOver H R (nclIn H (d1LayerX 3 H R)) →
    ∀ L₁ : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L₁ ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = L₁) →
      d1MapPCore 3 M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ L₁) ≠ ⊥ →
      d1MapPCore 3 M H ⊓ CFSG.pCore 3 (H ⧸ primeComplementCore (G := H) 3) = ⊥ →
      ¬ IsPGroup 3 (Subgroup.centralizer (L₁ : Set (H ⧸ primeComplementCore (G := H) 3))) →
      ∀ z : H, (z : G) ∈ R → orderOf z = 3 →
        QuotientGroup.mk' (primeComplementCore (G := H) 3) z ∈
          CFSG.pCore 3 (H ⧸ primeComplementCore (G := H) 3) →
        (z : G) ∈ nclIn M ⁅GLBPrimeCore 3 H, nclIn H (d1LayerX 3 H R)⁆ → False

@[expose] def D1CaseTwoUnique : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1CaseTwoData p P M H R Rbar →
    D1UniqueOver H R (nclIn H (d1LayerX p H R)) → False

@[expose] def CycAutRankLeTwo (p : ℕ) (Y : Type) [Group Y] [Finite Y] (Rb : Sylow p Y) : Prop :=
  ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y) →
    Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ 2

theorem ReducedNongeneration.cycAutRankLeTwo_of_kFactBeta {p : ℕ} {X : Type} [Group X]
    [Finite X] {R : Sylow p X} {X₀ : Subgroup X} (h : ReducedNongeneration p X R X₀)
    (hX : CatalogSimpleSections X) (hβ : KFactBeta) : CycAutRankLeTwo p X R :=
  fun _ hL hcyc => h.pRank_mulAut_le_two_of_isCyclic hX hβ hL hcyc

section Reduced

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {Rb : Sylow p Y} {Y₀ : Subgroup Y}

theorem ReducedNongeneration.exists_not_le_of_caseTwo_of_exists_component
    (h : ReducedNongeneration p Y Rb Y₀)
    (hA : CycAutRankLeTwo p Y Rb)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    (hK : ∃ K : Subgroup Y, IsComponentOf K ⊤) :
    ∃ L : Subgroup Y, IsComponentOf L ⊤ ∧ ¬ L ≤ Y₀ := by
  have hp := h.prime
  obtain ⟨K, hK⟩ := hK
  by_contra hex
  push Not at hex
  by_cases htwo : ∃ L : Subgroup Y, IsComponentOf L ⊤ ∧ L ≠ K
  · obtain ⟨L, hL, hLK⟩ := htwo
    exact h.false_of_two_components hK hL (Ne.symm hLK) hcyc hex
  push Not at htwo
  by_cases hO : CFSG.pCore p Y = ⊥
  · have hC := h.centralizer_eq_bot_of_unique_component htwo
      (h.center_eq_bot_of_isCyclic hK (hcyc K hK)) hO
    have h2 := pRank_le_pRank_inf_centralizer_add_pRank_mulAut hp
      (h.sylow_le_normalizer_component hK)
    have h4 := hA K hK (hcyc K hK)
    have h3' := h.three_le_pRank
    rw [hC, inf_bot_eq, pRank_bot_eq_zero hp] at h2
    omega
  · exact h.false_of_unique_component_of_pCore_ne_bot hK htwo (hcyc K hK) (hex K hK) hO

theorem ReducedNongeneration.exists_not_le_of_caseTwo_of_aut
    (h : ReducedNongeneration p Y Rb Y₀)
    (hA : CycAutRankLeTwo p Y Rb)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    {K : Subgroup Y} (hK : IsComponentOf K ⊤) :
    ∃ L : Subgroup Y, IsComponentOf L ⊤ ∧ ¬ L ≤ Y₀ :=
  h.exists_not_le_of_caseTwo_of_exists_component hA hcyc ⟨K, hK⟩

theorem ReducedNongeneration.pCore_ne_bot_of_unique_of_aut
    (h : ReducedNongeneration p Y Rb Y₀)
    (hA : CycAutRankLeTwo p Y Rb)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    (h3 : Open.pRank p (Rb : Subgroup Y) = 3) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (huniq : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → L' = L) : CFSG.pCore p Y ≠ ⊥ := by
  have hp := h.prime
  intro hO
  have hC := h.centralizer_eq_bot_of_unique_component huniq
    (h.center_eq_bot_of_isCyclic hL (hcyc L hL)) hO
  have h2 := pRank_le_pRank_inf_centralizer_add_pRank_mulAut hp
    (h.sylow_le_normalizer_component hL)
  have h4 := hA L hL (hcyc L hL)
  rw [hC, inf_bot_eq, pRank_bot_eq_zero hp] at h2
  omega

theorem ReducedNongeneration.exists_not_le_of_caseTwo (h : ReducedNongeneration p Y Rb Y₀)
    (hX : CatalogSimpleSections Y) (hβ : KFactBeta)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    {K : Subgroup Y} (hK : IsComponentOf K ⊤) :
    ∃ L : Subgroup Y, IsComponentOf L ⊤ ∧ ¬ L ≤ Y₀ :=
  h.exists_not_le_of_caseTwo_of_aut (h.cycAutRankLeTwo_of_kFactBeta hX hβ) hcyc hK

theorem ReducedNongeneration.pCore_ne_bot_of_unique (h : ReducedNongeneration p Y Rb Y₀)
    (hX : CatalogSimpleSections Y) (hβ : KFactBeta)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    (h3 : Open.pRank p (Rb : Subgroup Y) = 3) {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (huniq : ∀ L' : Subgroup Y, IsComponentOf L' ⊤ → L' = L) : CFSG.pCore p Y ≠ ⊥ :=
  h.pCore_ne_bot_of_unique_of_aut (h.cycAutRankLeTwo_of_kFactBeta hX hβ) hcyc h3 hL huniq

end Reduced

section Data

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoData.exists_not_le (hβ : KFactBeta) (hd : D1CaseTwoData p P M H R Rbar) :
    ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 p M H :=
  hd.cfg.red.exists_not_le_of_caseTwo_of_exists_component
    (hd.cfg.red.cycAutRankLeTwo_of_kFactBeta hd.cfg.catalog hβ) hd.cyclic
    hd.cfg.exists_isComponentOf

end Data

end CFSG.AGLEmbedding
