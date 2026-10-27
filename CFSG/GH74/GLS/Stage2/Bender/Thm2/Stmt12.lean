module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

@[expose] def Lemma12_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Stage2Ctx G z Kind.ly S →
    ∀ H : Subgroup G, H ≠ ⊤ → S ≤ H → ∀ V : Subgroup G, MaxSInv 3 S H V →
      (∀ V' : Subgroup G, MaxSInv 3 S H V' → ∃ c ∈ H ⊓ centralizer (S : Set G), V' = conjugate V c) ∧
      (¬ V ≤ pPrimeCoreOf 2 H → (IsDoubleCoverOfAlt (HBar H) 11 ∨ NativeSporadic.IsSporadic (HBar H) .Ly) ∧
        (V ⊓ pPrimeCoreOf 2 H).relIndex V = 3) ∧
      (Fs H = Op 3 H → H ≤ normalizer ((kInfty V : Subgroup G) : Set G) ∨
        (IsDoubleCoverOfAlt (HBar H) 11 ∧ H = pPrimeCoreOf 2 H ⊔ H ⊓ centralizer ((omega1Z 3 V : Subgroup G) : Set G)))

@[expose] def IVK_8_12_ly : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G), Stage2Ctx G z Kind.ly S →
    ∀ H : Subgroup G, H ≠ ⊤ → S ≤ H → ∀ V : Subgroup G, MaxSInv 3 S H V → ¬ V ≤ pPrimeCoreOf 2 H →
      (IsDoubleCoverOfAlt (HBar H) 11 ∨ NativeSporadic.IsSporadic (HBar H) .Ly) ∧
        (∀ V' : Subgroup G, MaxSInv 3 S H V' → ¬ V' ≤ pPrimeCoreOf 2 H →
          pPrimeCoreOf 2 H ⊔ V' = pPrimeCoreOf 2 H ⊔ V) ∧
        (V ⊓ pPrimeCoreOf 2 H).relIndex V = 3

@[expose] def Prop12_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (Q T U : Subgroup G) (t g : G),
    Ctx10 G z k S M p Q T U t g → ¬ (k = Kind.ly ∧ p = 3)

end CFSG.GH74.GLS.Stage2.Bender.Thm2
