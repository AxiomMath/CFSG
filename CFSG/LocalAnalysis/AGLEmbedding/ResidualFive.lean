module

public import CFSG.LocalAnalysis.AGLEmbedding.LemmaPThree
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveComponents
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoData
public import CFSG.LocalAnalysis.AGLEmbedding.BlockThree
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorusFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def GapR1bs : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig p P M H R Rbar →
    5 ≤ p → ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
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
        (∀ Lbar : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lbar ⊤ →
          barM M (d1LiftX p H R K) ≤ Subgroup.centralizer (Lbar : Set _)) →
        (∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p →
          ¬ barM M (d1LiftX p H R K) ≤ Subgroup.centralizer
            ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) →
          p < s) →
        ¬ ((d1LiftX p H R K ⊔ pCoreOf 2 M).subgroupOf M).Normal → False

theorem stmtFiveReduce_of (hC : StmtFiveComponents) (hO : StmtFiveOddCore) : StmtFiveReduce :=
  fun h hp => ⟨hC h hp, hO h hp⟩

theorem residualAt_five_of (hD : StmtL2Data) (h5 : StmtFiveReduce) (hgap : GapR1bs) :
    D1CaseThreeLinTwoResidualAt (5 ≤ ·) := by
  intro G _ _ p _ P M H R Rbar hcfg hp5 K hK huniq hnc hcent hKD d hd e hR1a
  obtain ⟨n, hdn⟩ := hd
  obtain ⟨hE, hO⟩ := h5 (hD G p P M H R Rbar hcfg K hK huniq hcent n d hdn e) hp5
  refine hgap G p P M H R Rbar hcfg hp5 K hK huniq hnc hcent hKD d ⟨n, hdn⟩ e hE ?_ hR1a
  intro s hs hs2 hsp hns
  by_contra hle
  exact hns (hO s hs hs2 (lt_of_le_of_ne (not_lt.mp hle) hsp))

theorem d1CaseThreeLinTwoResidual_closed (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hLB : StmtLemmaB) (hα : KFactThreeOrFiveDvd)
    (hβ : KFactOutElemRank) (hgap : GapR1bs) : D1CaseThreeLinTwoResidual :=
  have hB3 : StmtBlockThree := stmtBlockThree_of h85 h86 h93 hD2 hK2 hC3 hK5
  d1CaseThreeLinTwoResidual_of
    (residualAt_three_of_lemmaP3
      (lemmaP3LinTwo_of_inputs stmtL2Data h84 h85 hD2 hB3 hLB stmtPPDElement))
    (residualAt_five_of stmtL2Data
      (stmtFiveReduce_of
        (stmtFiveComponents_of
          (stmtROne_of hB3 hLB stmtPPDElement stmtNormalizeBlocks h85 hD2)
          (stmtFiveKComponents_of hα hβ stmtPPDElement stmtComponentRank stmtBarPRankLift))
        (stmtFiveOddCore_of h84 hD2))
      hgap)

end CFSG.AGLEmbedding
