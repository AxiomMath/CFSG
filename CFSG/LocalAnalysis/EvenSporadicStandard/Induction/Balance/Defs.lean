module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78

@[expose] def UGTSimpleStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ∀ z : G, orderOf z = 2 →
      CFSG.oddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ →
        CFSG.Blueprint.OddLieType G ∨
          ∃ n : ℕ, 7 ≤ n ∧ n % 4 = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin n))

@[expose] def IsAltType (X : Type) [Group X] : Prop :=
  ∃ n : ℕ, 5 ≤ n ∧ Nonempty (X ≃* alternatingGroup (Fin n))

@[expose] def CatalogNoRu : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N : Subgroup H), FStarSimple N → N.index ≤ 2 →
    CFSG.Blueprint.Catalog ↥N → ¬ IsAltType ↥N → ∀ (M : Subgroup H) (v : H), orderOf v = 2 →
      IsCompIn M (centralizer ({v} : Set H)) → OddCover .Ru M → False

@[expose] def CatalogFi23Host : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N : Subgroup H), FStarSimple N → N.index ≤ 2 →
    CFSG.Blueprint.Catalog ↥N → ¬ IsAltType ↥N → ∀ (L : Subgroup H) (t : H), orderOf t = 2 →
      IsCompIn L (centralizer ({t} : Set H)) → OddCover .Fi23 L →
        t ∉ N ∧ centralizer (L : Set H) = zpowers t

@[expose] def CatalogNoHSOdd : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N : Subgroup H), FStarSimple N → N.index ≤ 2 →
    CFSG.Blueprint.Catalog ↥N → ¬ IsAltType ↥N → ∀ (M : Subgroup H) (v : H), orderOf v = 2 →
      IsCompIn M (centralizer ({v} : Set H)) → OddCover .HS M → False

@[expose] def CatalogNoRuFull : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N : Subgroup H), FStarSimple N → N.index ≤ 2 →
    CFSG.Blueprint.Catalog ↥N → ∀ (M : Subgroup H) (v : H), orderOf v = 2 →
      IsCompIn M (centralizer ({v} : Set H)) → OddCover .Ru M → False

@[expose] def CatalogFi23HostFull : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N : Subgroup H), FStarSimple N → N.index ≤ 2 →
    CFSG.Blueprint.Catalog ↥N → ∀ (L : Subgroup H) (t : H), orderOf t = 2 →
      IsCompIn L (centralizer ({t} : Set H)) → OddCover .Fi23 L →
        t ∉ N ∧ centralizer (L : Set H) = zpowers t

end CFSG.EvenSporadicStandard.Induction.Balance
