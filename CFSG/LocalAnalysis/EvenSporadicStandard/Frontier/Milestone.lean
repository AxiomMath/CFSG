module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.EvenSporadicStandard.Frontier

open CFSG.Blueprint.NativeSporadic CFSG.Open CFSG.Milestones

@[expose] def OrderStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ (L : Subgroup G), standardComponentIsStandard L →
    (∀ t : G, orderOf t = 2 →
      standardComponentOddCore (Subgroup.centralizer ({t} : Set G)) = ⊥) →
    ∀ (S : Sylow 2 (Subgroup.centralizer (L : Set G))),
    IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))) →
    CFSG.Blueprint.Recognition.Exact.EvenStandardType (L ⧸ Subgroup.center L) →
    ¬ CFSG.Blueprint.Recognition.Exact.EvenStandardException (L ⧸ Subgroup.center L) →
    CFSG.Blueprint.Recognition.Exact.EvenStandardResidual L →
    CFSG.Blueprint.NativeSporadic.SporadicRep (L ⧸ Subgroup.center L) →
    (CFSG.Blueprint.NativeSporadic.IsSporadic (L ⧸ Subgroup.center L) .M12 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (L ⧸ Subgroup.center L) .J2 →
        Subgroup.center L = ⊥) →
    Nat.card G ∈ standardComponentEvenSporadicOrders

end CFSG.EvenSporadicStandard.Frontier
