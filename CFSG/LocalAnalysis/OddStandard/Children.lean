module

public import CFSG.Open.StandardComponentRecognitionMilestoneDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

structure StandardSetting (G : Type) [Group G] [Finite G] (L : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : CFSG.Assembly.KProper Blueprint.Catalog G
  standard : standardComponentIsStandard L

@[expose] def AltOutcome (G : Type) [Group G] : Prop :=
  ∃ m : ℕ, 9 ≤ m ∧ Nonempty (G ≃* alternatingGroup (Fin m))

@[expose] def ChildLargeAlt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    (∃ n : ℕ, 8 ≤ n ∧ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n))) →
    AltOutcome G ∨ IsSporadic G .McL ∨ IsSporadic G .Ly

@[expose] def ChildSmallAltOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    (∃ n : ℕ, 5 ≤ n ∧ n ≤ 7 ∧ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n))) →
    Odd (Nat.card (center L)) →
    AltOutcome G ∨ OddLieType G ∨
      (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS)

@[expose] def ChildSmallAltEven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    (∃ n : ℕ, 5 ≤ n ∧ n ≤ 7 ∧ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n))) →
    Even (Nat.card (center L)) → OddLieType G

@[expose] def ChildOddLie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    OddLieType (L ⧸ center L) →
    AltOutcome G ∨ OddLieType G ∨
      (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS)

@[expose] def ChildL34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    LieModel (L ⧸ center L) .PSL 3 2 2 →
    IsSporadic G .Suz ∨ IsSporadic G .He ∨ IsSporadic G .ONan

@[expose] def OddOutcome (G : Type) [Group G] : Prop :=
  AltOutcome G ∨ OddLieType G ∨
    (IsSporadic G .M12 ∨ IsSporadic G .J1 ∨ IsSporadic G .J2 ∨ IsSporadic G .HS ∨
      IsSporadic G .McL ∨ IsSporadic G .Ly ∨ IsSporadic G .Suz ∨ IsSporadic G .He ∨
      IsSporadic G .ONan)

end CFSG.OddStandard
