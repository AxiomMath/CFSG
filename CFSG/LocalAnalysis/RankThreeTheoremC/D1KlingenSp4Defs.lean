module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedClose3Klingen
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G]

@[expose] def IsKlingenIndex (p : ℕ) (d : TauCeti.ValidLieTypeIndex) : Prop :=
  IsSpFourIndex p d ∨ (p = 3 ∧ IsSpSixTwoIndex d)

@[expose] def IsKlingenComponent {Y : Type} [Group Y] (p : ℕ) (K : Subgroup Y) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, IsKlingenIndex p d ∧
    Nonempty (K ⧸ Subgroup.center K ≃* CatGroup d)

structure KFactKlingenLocal : Prop where
  outer : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (d : TauCeti.ValidLieTypeIndex),
    IsKlingenIndex p d → ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* CatGroup d) →
      ¬ p ∣ Nat.card (Outer K)
  inSitu : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (d : TauCeti.ValidLieTypeIndex),
    IsKlingenIndex p d → ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), K.Normal →
      Nonempty (K ≃* CatGroup d) →
      Subgroup.centralizer (K : Set Y) = ⊥ → ∀ (T : Sylow p Y) (B Y₀ : Subgroup Y),
        B ≤ T → IsElemAbelian p B → Nat.card B = p ^ 3 →
        GLBWeakCore p (T : Subgroup Y) ≤ Y₀ → Y₀ ≠ ⊤ → A3pInSitu p (T : Subgroup Y) B Y₀

structure StmtKlingenModel : Prop where
  center : ∀ (K : Type) [Group K] [Finite K] (p : ℕ) (d : TauCeti.ValidLieTypeIndex),
    p ≠ 2 → IsKlingenIndex p d → Open.IsQuasisimple K → IsPGroup p (Subgroup.center K) →
    Nonempty (K ⧸ Subgroup.center K ≃* CatGroup d) → Subgroup.center K = ⊥

@[expose] def D1KlingenSocle {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P : Sylow p G) (M R H : Subgroup G) : Prop :=
  ∃ (T : Type) (_ : Group T), IsSimpleGroup T ∧ (∃ a b : T, a * b ≠ b * a) ∧
    (∃ d : TauCeti.ValidLieTypeIndex, IsKlingenIndex p d ∧ Nonempty (T ≃* CatGroup d)) ∧
    D1SocleConfig T p P M H R R

@[expose] def D1CaseThreeKlingenOther3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) →
      ¬ IsKlingenComponent p K → False

@[expose] def StmtKlingenMSide3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) →
      (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
          Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)),
        orderOf c = p → c ∈ (Subgroup.center K).map K.subtype) →
      HasKlingenData p Rbar
        (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) →
      IsKlingenComponent p K → ∀ X : Subgroup G, D1SurvivorData p P M H R X →
      IsElemAbelian p X → Nat.card X = p ^ 3 →
      CFSG.pCore p (↥M ⧸ CFSG.pCore 2 ↥M) ≠ ⊥

structure D1KlingenResidue3 (G : Type) [Group G] [Finite G] : Prop where
  other : D1CaseThreeKlingenOther3 G
  mSide : StmtKlingenMSide3 G

theorem D1KlingenResidue3.of_klingen3 (h : D1CaseThreeKlingen3 G) : D1KlingenResidue3 G :=
  ⟨fun p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD _ =>
      h p P M H R Rbar hcfg K hK huniq hnc hcent hKD,
    fun p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD _ _ _ _ =>
      (h p P M H R Rbar hcfg K hK huniq hnc hcent hKD).elim⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
