module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Defs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

@[expose] def KFactKlingenThreeLocal : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex), IsKlingenIndex 3 d → ∀ (Y : Type) [Group Y] [Finite Y]
    [Fact (Nat.Prime 3)] (K : Subgroup Y), K.Normal → Nonempty (K ≃* CatGroup d) →
    Subgroup.centralizer (K : Set Y) = ⊥ → ∀ (T : Sylow 3 Y) (B Y₀ : Subgroup Y),
      B ≤ T → IsElemAbelian 3 B → Nat.card B = 3 ^ 3 → GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀ →
      Y₀ ≠ ⊤ → HasKlingenData 3 T Y₀ →
      A9InSitu (T : Subgroup Y) B Y₀ ∧ Nat.card (T : Subgroup Y) = 3 ^ 4 ∧
        Nat.card (centerOf (T : Subgroup Y)) = 3

@[expose] def StmtKlingenMSideFive3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 3 → ∀ (P : Sylow p G) (M H R : Subgroup G)
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

end CFSG.LocalAnalysis.RankThreeTheoremC
