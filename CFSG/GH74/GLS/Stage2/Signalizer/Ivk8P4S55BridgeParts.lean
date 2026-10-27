module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FrameParts

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

@[expose] def Lift55 : Prop :=
  P34.GHSchreier → ∀ (M : Type) [Group M] [Finite M] (p : ℕ) [Fact p.Prime], p ≠ 2 →
    pPrimeCore 2 M = ⊥ →
    (∀ J : Subgroup M, IsComponent J → GHList (↥J ⧸ center ↥J)) →
    (∀ J₁ J₂ J₃ : Subgroup M, IsComponent J₁ → IsComponent J₂ → IsComponent J₃ →
      J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ → False) →
    ∀ g : M, (∃ k : ℕ, g ^ p ^ k = 1) → pCore 2 M ≤ centralizer ({g} : Set M) →
    ∀ L W : Subgroup M, L.IsSubnormal → Group.IsPerfect ↥L → g ∈ normalizer (L : Set M) →
      W ≤ L → g ∈ normalizer (W : Set M) → ∀ _ : (W.subgroupOf L).Normal,
      IsSimpleGroup (↥L ⧸ W.subgroupOf L) →
      (∃ a b : ↥L ⧸ W.subgroupOf L, a * b ≠ b * a) →
      (∃ l ∈ L, ⁅l, g⁆ ∉ W) →
      ∃ J : Subgroup M, IsComponent J ∧ J ≤ L ∧ ¬ J ≤ W ∧ ¬ J ≤ centralizer ({g} : Set M)

@[expose] def Count55 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S T Tstar : Subgroup G) (p : ℕ)
    (H P : Subgroup G) (g : G) (X Y : Subgroup G), Cfg55 G z k S T Tstar p H P g X Y →
      ∀ J₁ J₂ J₃ : Subgroup (HBar H), IsComponent J₁ → IsComponent J₂ → IsComponent J₃ →
        J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ → False

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
