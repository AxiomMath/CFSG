module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Plus
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpE4Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer

@[expose] def P47BranchC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    E4Facts G z k →
    ∀ (Y : Type) [Group Y] [Finite Y] (b : Y), SecOfG G z Y b → b * b = 1 →
      ∀ (p : ℕ) (X : Subgroup Y), Sig4A b (⊤ : Subgroup Y) p X → pCore p Y = ⊥ →
        C43c b p X → C43cPlus p X →
        ∀ T' : Subgroup Y, IsPGroup 2 T' → T' ≤ centralizer ({b} : Set Y) →
          T' ≤ normalizer (X : Set Y) →
          ∀ E : Subgroup Y, E ≤ T' → CFSG.Open.IsElemAbelian 2 E → Nat.card ↥E ≤ 4

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
