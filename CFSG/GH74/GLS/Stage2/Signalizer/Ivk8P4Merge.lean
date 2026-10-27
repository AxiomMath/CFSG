module

public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt5

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

@[expose] def Lemma5_5m : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (T Tstar : Subgroup G) (p : ℕ) (H P : Subgroup G), Ctx51 k z S T Tstar p H P →
      ¬ Concl51 k S p H P → L52 k S T Tstar p H P →
      ∀ (g : G) (X Y : Subgroup G), Step53 p H P g X Y → L55 k p H

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
