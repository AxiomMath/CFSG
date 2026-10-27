module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1

@[expose] def IVK812Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Stage2Ctx G z Kind.ly S →
    ∀ H : Subgroup G, H ≠ ⊤ → S ≤ H → ∀ V : Subgroup G, MaxSInv 3 S H V → ¬ V ≤ pPrimeCoreOf 2 H →
      (IsDoubleCoverOfAlt (HBar H) 11 ∨ NativeSporadic.IsSporadic (HBar H) .Ly) ∧
        (NativeSporadic.IsSporadic (HBar H) .Ly →
          (∀ V' : Subgroup G, MaxSInv 3 S H V' → ¬ V' ≤ pPrimeCoreOf 2 H →
            pPrimeCoreOf 2 H ⊔ V' = pPrimeCoreOf 2 H ⊔ V) ∧
          (V ⊓ pPrimeCoreOf 2 H).relIndex V = 3)

@[expose] def LyInvariantThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], NativeSporadic.IsSporadic X .Ly →
    ∀ A : Subgroup X, Nat.card ↥A = 2 ^ 8 →
      ∀ W W' : Subgroup X, IsPGroup 3 ↥W → IsPGroup 3 ↥W' → W ≠ ⊥ → W' ≠ ⊥ →
        A ≤ normalizer (W : Set X) → A ≤ normalizer (W' : Set X) → W = W' ∧ Nat.card ↥W = 3

@[expose] def IVK812CoreA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Stage2Ctx G z Kind.ly S →
    ∀ H : Subgroup G, H ≠ ⊤ → S ≤ H → ∀ V : Subgroup G, MaxSInv 3 S H V → ¬ V ≤ pPrimeCoreOf 2 H →
      IsDoubleCoverOfAlt (HBar H) 11 ∨ NativeSporadic.IsSporadic (HBar H) .Ly

end CFSG.GH74.GLS.Stage2.Bender.Thm2
