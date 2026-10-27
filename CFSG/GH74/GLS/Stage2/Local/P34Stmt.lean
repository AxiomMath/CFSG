module

public import CFSG.GH74.GLS.Stage2.Local.Concl

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12

@[expose] def ConclA {G : Type} [Group G] (z : G) (H : Subgroup G) : Prop :=
  ∀ h ∈ H, ∃ c ∈ Cen z, ∃ o ∈ pPrimeCoreOf 2 H, h = c * o

@[expose] def FUS {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ u v : ↥H, orderOf u = 2 → orderOf v = 2 → IsConj (u : G) (v : G) →
    IsConj (QuotientGroup.mk u : HBar H) (QuotientGroup.mk v)

@[expose] def C0 {G : Type} [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G) (H : Subgroup G) : Prop :=
  ∃ (ε : Bool) (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)),
    k = Kind.l4 ε ∧ Stage1L4 G z S ε q L₁ L₂ ∧ 3 < q ∧
    IVK.IsPSp4 ↥(generalizedFitting (HBar H)) q ∧
    ¬ barIn H S ≤ generalizedFitting (HBar H) ∧ O2Of H ≠ H

@[expose] def NoOneClassC0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H → C0 z k S H →
      ¬ (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v)

@[expose] def PerfInJ {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ P : Subgroup G, P ≤ H → Group.IsPerfect ↥P → barIn H P ≤ generalizedFitting (HBar H)

@[expose] def GHSchreier : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → (∃ a b : J, a * b ≠ b * a) → GHList J →
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer J)

@[expose] def IVK93 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H → pCore 2 (HBar H) = ⊥ →
      IsSimpleGroup ↥(generalizedFitting (HBar H)) →
      (∃ a b : ↥(generalizedFitting (HBar H)), a * b ≠ b * a) →
      PerfInJ H → HasTwoInvolutionClasses (HBar H) → C0 z k S H ∨ FUS H

@[expose] def Prop34M12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Stage2Ctx G z Kind.m12 S →
    ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H → pCore 2 (HBar H) ≠ ⊥ → ConclA z H

end CFSG.GH74.GLS.Stage2.Local.P34
