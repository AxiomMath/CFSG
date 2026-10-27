module

public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def IsSpSixTwoIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .B 3 q

@[expose] def Sp62BlockShape {G : Type} [Group G] (M H R L : Subgroup G) : Prop :=
  IsWeakSBlock M (pCoreOf 2 H) L ∧
  (∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' → barM M L' = barM M L) ∧
  (barM M L).Normal ∧ barM M R ≤ barM M L ∧ CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) = ⊥ ∧
  ((∃ d : TauCeti.ValidLieTypeIndex, IsUSixTwoIndex d ∧ Nonempty (barM M L ≃* CatGroup d) ∧
      (blockParabolic M (pCoreOf 2 H) L).relIndex (barM M L) = 693) ∨
    ∃ (m : ℕ) (d : TauCeti.ValidLieTypeIndex), 4 ≤ m ∧ IsOmegaMinusTwoIndex m d ∧
      Nonempty (barM M L ≃* CatGroup d) ∧
      (blockParabolic M (pCoreOf 2 H) L).relIndex (barM M L) = omegaMinusFlagIndex m)

@[expose] def D1Sp62BlockResidue : Prop :=
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
      ∀ d : TauCeti.ValidLieTypeIndex, p = 3 → IsSpSixTwoIndex d →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        ∀ L : Subgroup G, Sp62BlockShape M H R L → False

end CFSG.AGLEmbedding
