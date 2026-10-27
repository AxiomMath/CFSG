module

public import CFSG.LocalAnalysis.OddStandard.Children
public import CFSG.GroupTheory.PCore.Defs

public section

namespace CFSG.OddStandard.SmallF3

open Subgroup CFSG.Blueprint

structure SmallF3Cyclic (G : Type) [Group G] [Finite G] (L : Subgroup G) : Prop
    extends StandardSetting G L where
  balanced : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥
  cyclic : ∀ S : Sylow 2 (centralizer (L : Set G)),
    IsCyclic (S : Subgroup (centralizer (L : Set G)))
  centre : center L = ⊥ ∨
    (LieModel (L ⧸ center L) .PSU 4 3 1 ∧ Nat.card (center L) = 2)

@[expose] def SmallF3OmegaQuotient (Q : Type) [Group Q] : Prop :=
  LieModel Q .PSp 2 3 1 ∨ LieModel Q .PSL 4 3 1 ∨ LieModel Q .PSU 4 3 1 ∨
    LieModel Q .POmegaOdd 3 3 1 ∨ LieModel Q .POmegaPlus 4 3 1 ∨ LieModel Q .POmegaMinus 4 3 1

@[expose] def SmallF3L33Block : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SmallF3Cyclic G L →
    LieModel (L ⧸ center L) .PSL 3 3 1 → OddLieType G

@[expose] def SmallF3U33Block : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SmallF3Cyclic G L →
    LieModel (L ⧸ center L) .PSU 3 3 1 → OddLieType G

@[expose] def SmallF3OmegaBlock : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SmallF3Cyclic G L →
    SmallF3OmegaQuotient (L ⧸ center L) → OddLieType G

end CFSG.OddStandard.SmallF3
