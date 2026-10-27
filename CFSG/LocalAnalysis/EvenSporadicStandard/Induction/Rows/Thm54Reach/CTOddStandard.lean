module

public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.Blueprint.OddStandardExact

public section

namespace CFSG.EvenSporadicStandard.Induction

@[expose] def CTOddStandardStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G →
    ∀ (L : Subgroup G), CFSG.Open.standardComponentIsStandard L →
    CFSG.Blueprint.Recognition.Exact.OddStandardType (L ⧸ Subgroup.center L) →
    (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨ CFSG.Blueprint.OddLieType G ∨
      (CFSG.Blueprint.NativeSporadic.IsSporadic G .M12 ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic G .J1 ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic G .J2 ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic G .HS ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic G .McL ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic G .Ly ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic G .Suz ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic G .He ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic G .ONan)

end CFSG.EvenSporadicStandard.Induction
