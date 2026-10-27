module

public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.Blueprint.EvenStandardExact

public section

namespace CFSG.EvenSporadicStandard.Induction

@[expose] def CTEvenSmallLieStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ (L : Subgroup G), CFSG.Open.standardComponentIsStandard L →
    (∀ t : G, orderOf t = 2 →
      CFSG.Open.standardComponentOddCore (Subgroup.centralizer ({t} : Set G)) = ⊥) →
    ∀ (S : Sylow 2 (Subgroup.centralizer (L : Set G))),
      IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))) →
      CFSG.Blueprint.Recognition.Exact.EvenStandardType (L ⧸ Subgroup.center L) →
      ¬ CFSG.Blueprint.Recognition.Exact.EvenStandardException (L ⧸ Subgroup.center L) →
      CFSG.Blueprint.Recognition.Exact.EvenStandardResidual L →
      (CFSG.Blueprint.Recognition.Exact.ResidualB L ∨
        CFSG.Blueprint.Recognition.Exact.ResidualC L ∨
        CFSG.Blueprint.Recognition.Exact.ResidualD L) →
      CFSG.Blueprint.Recognition.EvenSporadicOutcome G

end CFSG.EvenSporadicStandard.Induction
