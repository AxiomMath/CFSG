module

public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt5

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg

@[expose] def Lemma5_2One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (T Tstar : Subgroup G) (p : ℕ) (H P : Subgroup G), Ctx51 k z S T Tstar p H P →
      (TypeOneCase G k ∧ T = S ∧ Tstar = S) → L52 k S T Tstar p H P

@[expose] def Lemma5_2Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ (T Tstar : Subgroup G) (p : ℕ) (H P : Subgroup G), Ctx51 k z S T Tstar p H P →
      ¬ TypeOneCase G k → ¬ Concl51 k S p H P → L52 k S T Tstar p H P

theorem lemma5_2_of_halves (h1 : Lemma5_2One) (h2 : Lemma5_2Two) : Lemma5_2 := by
  intro G _ _ z k S ctx T Tstar p H P hctx hnc
  rcases hctx.T5 with h | ⟨h, -⟩
  · exact h1 G z k S ctx T Tstar p H P hctx h
  · exact h2 G z k S ctx T Tstar p H P hctx h hnc

end CFSG.GH74.GLS.Stage2.Signalizer
