module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypNF

public section

namespace CFSG.ComponentClassification.RankTwoL3Four

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.ComponentClassification.RankTwoStandard

@[expose] def OddCoreFreeConclusion {G : Type} [Group G] (A : Subgroup G) : Prop :=
  IsSporadic (rankTwoX A) .Suz ∨
    (Nonempty (center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
      IsSporadic (rankTwoX A) .He)

@[expose] def L34Conclusion {G : Type} [Group G] (A : Subgroup G) : Prop :=
  (IsSporadic (rankTwoX A ⧸ center (rankTwoX A)) .Suz ∧ Nat.card (center (rankTwoX A)) ∣ 3) ∨
    (Nonempty (center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
      IsSporadic (rankTwoX A) .He)

@[expose] def L34OddCoreFree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
    Assembly.LowTwoRank.StatedClassicalModel (rankTwoQuot A) .PSL 3 2 2 →
    standardComponentOddCore G = ⊥ → OddCoreFreeConclusion A

@[expose] def L34General : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
    Assembly.LowTwoRank.StatedClassicalModel (rankTwoQuot A) .PSL 3 2 2 → L34Conclusion A

@[expose] def L34GeneralBelow (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), Nat.card G < n → RankTwoHypNF G A →
    Assembly.LowTwoRank.StatedClassicalModel (rankTwoQuot A) .PSL 3 2 2 → L34Conclusion A

@[expose] def SuzMultiplierSix : Prop :=
  ∀ (E : Type) [Group E] [Finite E], Group.IsPerfect E → ∀ π : E →* NativeSporadic.Suz,
    Function.Surjective π → π.ker ≤ center E → Nat.card π.ker ∣ 6

end CFSG.ComponentClassification.RankTwoL3Four
