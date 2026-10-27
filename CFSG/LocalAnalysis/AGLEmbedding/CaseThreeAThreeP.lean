module

public import CFSG.LocalAnalysis.AGLEmbedding.AThreePLift

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1CaseThreeA15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fact (Nat.Prime 5)] (P : Sylow 5 G)
    (M H R : Subgroup G) (Rbar : Sylow 5 (H ⧸ primeComplementCore (G := H) 5)),
    D1ComponentConfig 5 P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 5), IsComponentOf K ⊤ →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 5), IsComponentOf L ⊤ → L = K) →
    ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 5)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) 5)) →
    (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 5)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 5)),
      orderOf c = 5 → c ∈ (Subgroup.center K).map K.subtype) →
    ¬ HasKlingenData 5 Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5))) →
    Subgroup.center K = ⊥ → Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 15)) →
    False

@[expose] def D1CaseThreeA9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [Fact (Nat.Prime 3)] (P : Sylow 3 G)
    (M H R : Subgroup G) (Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)),
    D1ComponentConfig 3 P M H R Rbar →
    ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf K ⊤ →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) 3), IsComponentOf L ⊤ → L = K) →
    ¬ IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K :
      Subgroup (H ⧸ primeComplementCore (G := H) 3)) →
    (∀ c ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)),
      orderOf c = 3 → c ∈ (Subgroup.center K).map K.subtype) →
    ¬ HasKlingenData 3 Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3))) →
    Subgroup.center K = ⊥ → Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 9)) →
    False

theorem d1CaseThreeA3p_of (hT : ThompsonNormalAbelianGen) (h15 : D1CaseThreeA15)
    (h9 : D1CaseThreeA9) : D1CaseThreeA3p :=
  d1CaseThreeA3p_of_guest (a3pGuestLift_of hT) h15 h9

end CFSG.AGLEmbedding
