module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoJConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1CaseThreeLinTwoResidual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ¬ HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) →
      ∀ d : TauCeti.ValidLieTypeIndex, (∃ n, IsLinTwoIndex p n d) →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ¬ ((d1LiftX p H R K ⊔ pCoreOf 2 M).subgroupOf M).Normal → False

@[expose] def D1CaseThreeLieAt (S : ℕ → TauCeti.ValidLieTypeIndex → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ¬ HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) →
      ∀ d : TauCeti.ValidLieTypeIndex, S p d →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) → False

theorem d1CaseThreeLie_of_split (hP1 : KFactP1ThreeLie) (hKl : KFactKlingenSpFour)
    (hL2 : D1CaseThreeLieAt fun p d => ∃ n, IsLinTwoIndex p n d)
    (hU : D1CaseThreeLieAt IsUnitaryIndex) (hRee : D1CaseThreeLieAt IsReeGTwoIndex)
    (hC2 : D1CaseThreeLieAt IsP1ChevTwoIndex) :
    D1CaseThreeLie := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d e
  rcases hP1 p _ Rbar _ hcfg.red hcfg.catalog K hK huniq hnc hcent d e with
    h | h | h | h | h
  · exact hL2 G p P M H R Rbar hcfg K hK huniq hnc hcent hKD d h e
  · exact hU G p P M H R Rbar hcfg K hK huniq hnc hcent hKD d h e
  · exact hRee G p P M H R Rbar hcfg K hK huniq hnc hcent hKD d h e
  · exact hKD (hKl p _ Rbar _ hcfg.red hcfg.catalog K hK huniq hnc hcent d h e)
  · exact hC2 G p P M H R Rbar hcfg K hK huniq hnc hcent hKD d h e

theorem d1CaseThreeLinTwo_of
    (hC : StmtCompetitor) (hCGT : AschbacherLocalCGTBlock) (hD2 : D1NoXBlock)
    (hres : D1CaseThreeLinTwoResidual) :
    D1CaseThreeLieAt fun p d => ∃ n, IsLinTwoIndex p n d := by
  have hA := @stmtL2ConfigOfComponent
  have hB := @stmtToD1JConfig
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨n, hd⟩ e
  by_cases hR1a : ((d1LiftX p H R K ⊔ pCoreOf 2 M).subgroupOf M).Normal
  · exact false_of_competitorsOn (C := fun H' => D1L2Config p n P M H' R (d1LiftX p H R K))
      (fun _ h => hB h) hC (hA hcfg hK huniq hcent hd e hR1a) hCGT hD2
  · exact hres G p P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨n, hd⟩ e hR1a

@[expose] def D1CaseThreeLinTwoResidualAt (S : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
    S p → ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ¬ HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) →
      ∀ d : TauCeti.ValidLieTypeIndex, (∃ n, IsLinTwoIndex p n d) →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ¬ ((d1LiftX p H R K ⊔ pCoreOf 2 M).subgroupOf M).Normal → False

@[expose] def StmtLemmaP3LinTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
    p = 3 → ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      ¬ HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) →
      ∀ d : TauCeti.ValidLieTypeIndex, (∃ n, IsLinTwoIndex p n d) →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ((d1LiftX p H R K ⊔ pCoreOf 2 M).subgroupOf M).Normal

theorem residualAt_three_of_lemmaP3 (hP3 : StmtLemmaP3LinTwo) :
    D1CaseThreeLinTwoResidualAt (· = 3) := by
  intro G _ _ p _ P M H R Rbar hcfg hp3 K hK huniq hnc hcent hKD d hd e hR1a
  exact hR1a (hP3 G p P M H R Rbar hcfg hp3 K hK huniq hnc hcent hKD d hd e)

theorem d1CaseThreeLinTwoResidual_of (h3 : D1CaseThreeLinTwoResidualAt (· = 3))
    (h5 : D1CaseThreeLinTwoResidualAt (5 ≤ ·)) : D1CaseThreeLinTwoResidual := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd e hR1a
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hcfg.red.ne_two
  rcases (show p = 3 ∨ 5 ≤ p by
      have := hp.two_le
      rcases Nat.lt_or_ge p 5 with h | h
      · interval_cases p
        · exact absurd rfl hp2
        · exact Or.inl rfl
        · exact absurd hp (by decide)
      · exact Or.inr h) with h | h
  · exact h3 G p P M H R Rbar hcfg h K hK huniq hnc hcent hKD d hd e hR1a
  · exact h5 G p P M H R Rbar hcfg h K hK huniq hnc hcent hKD d hd e hR1a

theorem d1CaseThreeLinTwo_closed (hβ : KFactBeta) (hP1L : KFactP1ThreeLie)
    (hP1A : KFactP1ThreeAlt) (hP1S : KFactP1ThreeSpor) (hEL : KFactJStarElimLie)
    (hEA : KFactJStarElimAlt) (hES : KFactJStarElimSpor) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : D1NoXBlock) (hres : D1CaseThreeLinTwoResidual) :
    D1CaseThreeLieAt fun p d => ∃ n, IsLinTwoIndex p n d :=
  d1CaseThreeLinTwo_of
    (stmtCompetitor hβ hP1L hP1A hP1S hEL hEA hES) hCGT hD2 hres

end CFSG.AGLEmbedding
