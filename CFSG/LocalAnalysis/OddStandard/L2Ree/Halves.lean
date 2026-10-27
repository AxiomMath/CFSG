module

public import CFSG.LocalAnalysis.OddStandard.Children
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalUnbalanced
public import CFSG.Open.GriessSchurMultipliersMilestoneDefs
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.OddStandard.L2Ree

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def L2Half : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    OddLieType (L ⧸ center L) →
    (∃ p f : ℕ, LieModel (L ⧸ center L) .PSL 2 p f) →
    ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 5)) →
    ¬ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 6)) →
    (Odd (Nat.card (center L)) ∨
      ∃ p n r : ℕ, p.Prime ∧ p ≠ 2 ∧ 0 < n ∧ 0 < r ∧
        (LieModel (L ⧸ center L) .PSL (2 * n) p r ∨ LieModel (L ⧸ center L) .PSU (2 * n) p r) ∧
        ordProj[2] (Nat.card (center L)) ≠
          ordProj[2] (Nat.card (Open.griessHopfMultiplier (L ⧸ center L)))) →
    ∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))) →
      AltOutcome G ∨ OddLieType G ∨
        (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS)

@[expose] def ReeHalf : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    ((∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set G)) ≠ ⊥) →
      ComponentClassification.OutcomeLocal.UOutcome G) →
    (∃ f : ℕ, LieModel (L ⧸ center L) .twistedG2 0 3 f) →
    ∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))) →
      AltOutcome G ∨ OddLieType G ∨
        (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS)

end CFSG.OddStandard.L2Ree
