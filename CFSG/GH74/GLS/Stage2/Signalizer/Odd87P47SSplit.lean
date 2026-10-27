module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47SStmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer

@[expose] def P47BranchSL2b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    E4Facts G z k →
    ∀ (Y : Type) [Group Y] [Finite Y] (b : Y), SecOfG G z Y b → b * b = 1 →
      ∀ (p : ℕ) (X : Subgroup Y), Sig4A b (⊤ : Subgroup Y) p X → pCore p Y = ⊥ → C43b p X →
        ∀ T' : Subgroup Y, IsPGroup 2 T' → T' ≤ centralizer ({b} : Set Y) →
          T' ≤ normalizer (X : Set Y) →
          ∀ E : Subgroup Y, E ≤ T' → CFSG.Open.IsElemAbelian 2 E → Nat.card ↥E ≤ 8

@[expose] def P47BranchSL2e : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    E4Facts G z k →
    ∀ (Y : Type) [Group Y] [Finite Y] (b : Y), SecOfG G z Y b → b * b = 1 →
      ∀ (p : ℕ) (X : Subgroup Y), Sig4A b (⊤ : Subgroup Y) p X → pCore p Y = ⊥ → C43e X →
        ∀ T' : Subgroup Y, IsPGroup 2 T' → T' ≤ centralizer ({b} : Set Y) →
          T' ≤ normalizer (X : Set Y) →
          ∀ E : Subgroup Y, E ≤ T' → CFSG.Open.IsElemAbelian 2 E → Nat.card ↥E ≤ 8

theorem p47BranchSL2_of (hb : P47BranchSL2b) (he : P47BranchSL2e) : P47BranchSL2 := by
  intro G _ _ z k S ctx F4 Y _ _ b hY hb2 p X hA hop hc T' hT2 hTc hTn E hET hE
  rcases hc with hc | hc
  · exact hb G z k S ctx F4 Y b hY hb2 p X hA hop hc T' hT2 hTc hTn E hET hE
  · exact he G z k S ctx F4 Y b hY hb2 p X hA hop hc T' hT2 hTc hTn E hET hE

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
