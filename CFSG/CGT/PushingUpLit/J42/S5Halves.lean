module

public import CFSG.CGT.PushingUpLit.J42.NarrowS5

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.GH74 Equiv Equiv.Perm
open CFSG.Assembly (InCatalog KProper)

@[expose] def JankoU42Gen4S5ROne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M X : Subgroup G) (S : SolCfg G M X 2),
    KProper InCatalog G → TightData S → RSmall S → ¬ CentInM S →
      (∃ m : ↥M, sign (S.θ m) = -1) → rOf M X = ⊥ → SectionalTwoRankLE G 4

@[expose] def JankoU42Gen4S5RNe1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M X : Subgroup G) (S : SolCfg G M X 2),
    KProper InCatalog G → TightData S → RSmall S → ¬ CentInM S →
      (∃ m : ↥M, sign (S.θ m) = -1) → rOf M X ≠ ⊥ → SectionalTwoRankLE G 4

theorem jankoU42Gen4S5_of_halves (h1 : JankoU42Gen4S5ROne) (h2 : JankoU42Gen4S5RNe1) :
    JankoU42Gen4S5 := by
  intro G _ _ M X S hKP hT hR hC hA
  by_cases hr : rOf M X = ⊥
  · exact h1 G M X S hKP hT hR hC hA hr
  · exact h2 G M X S hKP hT hR hC hA hr

end CFSG.CGT.PushingUpLit.SolK
