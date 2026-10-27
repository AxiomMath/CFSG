module

public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTheoremZ
public import CFSG.LocalAnalysis.AGLEmbedding.D1ConfigU
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaLists
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Defs

variable {G : Type} [Group G] [Finite G]

structure D1OneLieData (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop where
  cfg : D1ComponentConfigU p P M H R Rbar
  comp : IsComponentOf K ⊤
  center : Subgroup.center K = ⊥
  noncyclic : ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
    Subgroup (H ⧸ primeComplementCore (G := H) p))
  z : ∃ z ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)), z ∉ K ∧ orderOf z = p ∧
    z ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))
  big : ¬ Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2

theorem D1OneLieData.glob {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : D1OneLieData p P M H R Rbar K) :
    CFSG.AGLEmbeddingD2.AGLGlobal G :=
  hd.cfg.glob.toAGLGlobal

theorem D1OneLieData.toD1ComponentConfig {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hd : D1OneLieData p P M H R Rbar K)
    (h4 : 4 ≤ evenRank G) : D1ComponentConfig p P M H R Rbar :=
  hd.cfg.toD1ComponentConfig h4

theorem D1ComponentConfigU.map_d1LiftX_eq_inf {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hcfg : D1ComponentConfigU p P M H R Rbar) :
    ((d1LiftX p H R K).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K := by
  rw [map_d1LiftX, hcfg.rbar]

@[expose] def D1CaseOneLieBigAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneLieData p P M H R Rbar K → False

@[expose] def D1CaseOneLieBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G], 4 ≤ evenRank G → D1CaseOneLieBigAt G

@[expose] def D1OneLieClass (p : ℕ) (P : Sylow p G) (M R X H : Subgroup G) : Prop :=
  ∃ (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    D1OneLieData p P M H R Rbar K ∧ d1LiftX p H R K = X

@[expose] def d1MapPCore (p : ℕ) (M H : Subgroup G) :
    Subgroup (H ⧸ primeComplementCore (G := H) p) :=
  ((pCorePreimage p M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))

@[expose] def d1PlusCore (p : ℕ) (H : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Subgroup G :=
  ((Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p))).comap
    (QuotientGroup.mk' (primeComplementCore (G := H) p))).map H.subtype

@[expose] def D1UniqueOver (H R J : Subgroup G) : Prop :=
  ∀ H' : Subgroup G, GLBIsMaxTwoLocal H' → J ≤ H' → R ≤ H' → H' = H

theorem D1UniqueOverJ.toUniqueOver {p : ℕ} {H R J : Subgroup G} (h : D1UniqueOverJ p H R J)
    (hR : IsPGroup p R) : D1UniqueOver H R J :=
  fun H' hH' hJH' hRH' => h H' hH' hJH' R hRH' hR le_rfl le_rfl

end Defs

@[expose] def IsUnitaryGroup (p : ℕ) (K : Type) [Group K] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, IsUnitaryIndex p d ∧
    Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)

open CFSG.ComponentClassification.OuterAutomorphisms in
structure OneLieFacts (p : ℕ) (K : Type) [Group K] [Finite K] (T : Sylow p K) : Prop where
  uPrime : KFactUPrime p K
  outer_solvable : Group.IsSolvable (Outer K)
  pSubgroup_le : ∀ Y : Subgroup (MulAut K), IsPGroup p Y →
    Y ≤ Subgroup.normalizer (((T : Subgroup K).map (MulAut.conj : K →* MulAut K) :
      Subgroup (MulAut K)) : Set (MulAut K)) →
    (Subgroup.normalizer ((T : Subgroup K) : Set K)).map (MulAut.conj : K →* MulAut K) ≤
      Subgroup.normalizer (Y : Set (MulAut K)) →
    Y ≤ (T : Subgroup K).map (MulAut.conj : K →* MulAut K)
  torus : ∃ T₀ : Subgroup K, T₀ ≤ Subgroup.normalizer ((T : Subgroup K) : Set K) ∧
    p.Coprime (Nat.card T₀) ∧ (T : Subgroup K) ⊓ Subgroup.centralizer (T₀ : Set K) = ⊥
  centralizer : ∀ V : Subgroup K, V ≤ T → V ≠ ⊥ →
    Subgroup.normalizer ((T : Subgroup K) : Set K) ≤ Subgroup.normalizer (V : Set K) →
    (∀ f : MulAut K, (∀ v ∈ V, f v = v) → ∃ t ∈ (T : Subgroup K), f = MulAut.conj t) ∨
      (V = centerOf (T : Subgroup K) ∧ IsUnitaryGroup p K)

@[expose] def KFactOneLie : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    IsCatalogGroup K → ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ T : Sylow p K,
      ¬ IsCyclic (T : Subgroup K) → GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      ¬ Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 → OneLieFacts p K T

@[expose] def D1OneLieMSide : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneLieData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥

@[expose] def D1OneLieMSideCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneLieData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) →
    ∃ X₁ : Subgroup G, X₁ ≤ d1LiftX p H R K ∧ X₁ ≠ ⊥ ∧
      (∀ L : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf L ⊤ →
        barM M X₁ ≤ Subgroup.centralizer (L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) ∧
      ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p →
        barM M X₁ ≤ Subgroup.centralizer
          ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
            Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∨
        4 ≤ Open.pRank s (((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)).comap
          (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype)

@[expose] def D1OneLieU3Z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneLieData p P M H R Rbar K →
    D1UniqueOver H R (nclIn H (d1LiftX p H R K)) → pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ →
    IsUnitaryGroup p K →
    d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
      centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) → False

@[expose] def D1OneLieZZa : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneLieData p P M H R Rbar K →
    D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)) →
    pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
    d1MapPCore p M H ≤ K →
    ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) →
    (∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) → IsPGroup 2 W →
      ¬ 2 ∣ (W.subgroupOf (Subgroup.centralizer
        (K : Set (H ⧸ primeComplementCore (G := H) p)))).index →
      ¬ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p))) → False

@[expose] def D1OneLieZZb : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneLieData p P M H R Rbar K →
    D1UniqueOverJ p H R (nclIn H (d1LiftX p H R K)) →
    pCorePreimage p M ⊓ d1LiftX p H R K ≠ ⊥ →
    (∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧ L ≠ K) →
    d1MapPCore p M H ≤ K →
    ¬ (IsUnitaryGroup p K ∧
      d1MapPCore p M H ⊓ ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K) =
        centerOf ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)) →
    (∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) → IsPGroup 2 W →
      ¬ 2 ∣ (W.subgroupOf (Subgroup.centralizer
        (K : Set (H ⧸ primeComplementCore (G := H) p)))).index →
      ¬ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p))) → False

@[expose] def D1OneLieResidue : Prop := D1OneLieZZa ∧ D1OneLieZZb ∧ D1OneLieU3Z

theorem d1CaseOneLieAt_of_big {G : Type} [Group G] [Finite G]
    (h1s : D1CaseOneSmallAt G) (hb : D1CaseOneLieBigAt G) : D1CaseOneLieAt G := by
  intro p P M H R Rbar hcfg K hK hZ hnc hz _
  by_cases hAut : Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2
  · obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hz
    obtain ⟨-, hKX₀⟩ := hcfg.red.rankOne_principle hK hnc hzR hzK hzp hzc
    exact h1s p P M H R Rbar hcfg K hK hZ hnc ⟨z, hzR, hzK, hzp, hzc⟩ hAut
      (hcfg.red.pRank_eq_three_of_pRank_mulAut_le_two hK hKX₀ hAut)
  · exact hb p P M H R Rbar K ⟨hcfg, hK, hZ, hnc, hz, hAut⟩

theorem d1CaseOneLie_of_big (h1s : D1CaseOneSmall) (hb : D1CaseOneLieBig) : D1CaseOneLie :=
  d1CaseOneLie_of_at fun _ _ _ h4 => d1CaseOneLieAt_of_big (h1s.toAt h4) (hb _ h4)

end CFSG.AGLEmbedding
