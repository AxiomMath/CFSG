module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Proved
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Slots
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.K2Core
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.InnDiagRank
public import CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.FactorThreePrimeProof
public import CFSG.Quasithin.Vol2.Ch11SecOE5B

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def SlotP614Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G →
    ∀ (P : Sylow 3 G) (M : Subgroup G) (x z : G) (T : Subgroup G),
      Prop627Failure G 3 P M x z T → ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
        zpowers z ≤ normalizer (S₀ : Set G) → normalizer (S₀ : Set G) ≤ M

@[expose] def SlotFitting628Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G →
    ∀ (P : Sylow 5 G) (M : Subgroup G) (x z : G) (T : Subgroup G),
      Prop627Failure G 5 P M x z T → SmallRankCover 5 M x →
        smallRankIsQ8D8 (smallRankR x z T) →
          CFSG.fittingSubgroupOf (rankThreePrimeCore 2 (smallRankD 5 x)) ⊓ M = ⊥

@[expose] def SlotP614CaseDelta : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G →
    ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M → ∀ x z : G,
      SmallRankPoint P M x → SmallRankCentral P z → SmallRankCaseDelta3 P M →
        Fail614NormalizerRank P M (zpowers x ⊔ zpowers z)

@[expose] def SlotP614Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → Prop614FailCore G

section Frontier

theorem kfactRankThreeStructure_proved
    : KFactRankThreeStructure :=
  KFactProofs.K2.kfactRankThreeStructure_of_core
    (KFactProofs.T29.kfactRankThreeCore_of_T29
      (KFactProofs.T29.gl83I291Three_of_families (KFactProofs.T29.noncyclicCentreRank_of_tables
          (CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement)
          (CFSG.HardMathSupport.Timmesfeld.Coordinator.sporadicMultipliers_of_census
              CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds))
        KFactProofs.T29.altTripleCoverAbelianBound_holds KFactProofs.T29.t29Spor_holds
        KFactProofs.T29.t29Chev3_holds (KFactProofs.T29.Parrott.t29ChevOther_of_kfacts
            KFactProofs.T29.Parrott.t29LThreeEpsCase_holds
            KFactProofs.T29.Parrott.outerFixedE9_holds
            KFactProofs.T29.Parrott.innerFusionE9Exc_holds))
      KFactProofs.T29.innDiagRankTwo_holds
      CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.input23_16Three_holds)

theorem slotP614Three_of
    (hδ : SlotP614CaseDelta) (hcore : SlotP614Core) : SlotP614Three :=
  fun G _ _ hS hD1 =>
    prop614_failing_three_of_core_of_d1 hS hD1 kFactBlockFactorThreePrime_of_cgtBlock
      (fun P M hsit x z hx hz => gl83SmallRankLemma62At3_proved G hS
        (fullCoreLocal_of_theoremD1_situation_three hS hD1 hsit) P M hsit x z hx hz)
      (hδ G hS hD1) (hcore G hS hD1)

end Frontier

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
