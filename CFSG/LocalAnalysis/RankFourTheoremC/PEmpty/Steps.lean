module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Extremal

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def StepL63 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z → ¬ HasPrimeConstraint (G := M) p →
      NormalizerRank p P M (zpowers x ⊔ zpowers z)

@[expose] def StepL617 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z → ∀ H S : Subgroup G, Optimal p M x z H S →
      GLBPrimeCore p H ≤ M

@[expose] def StepKGroup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G),
    Situation G p P M → Point P M x → Central P z → ∀ H S : Subgroup G, Optimal p M x z H S →
      GLBPrimeCore p H ≤ M → False

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
