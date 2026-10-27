module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs18

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

@[expose] def Lemma17_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Fail17 G z k S M →
    OddCover z M → ∀ J : Subgroup G, IsPCompIn 2 M J →
      pRank 2 ↥(M ⊓ centralizerSection J (pPrimeCoreOf 2 J)) = 1

@[expose] def Lemma17_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Fail17 G z k S M →
    Em M ≠ ⊥ →
      (pRank 2 ↥(Em M) = 1 ∧ z ∈ Em M ∧ k = Kind.g2) ∧
      (pLayerOf 2 M = Em M → G2Three z S ∧
        O22Of (O2Of M) = pPrimeCoreOf 2 (O22Of (O2Of M)) ⊔ (S ⊓ O22Of (O2Of M)) ∧
        Nonempty (↥(S ⊓ O22Of (O2Of M)) ≃* QuaternionGroup 2) ∧
        S ⊓ O22Of (O2Of M) ⊓ centralizer (pPrimeCoreOf 2 (O22Of (O2Of M)) : Set G) = zpowers z)

@[expose] def Lemma17_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Fail17 G z k S M →
    pLayerOf 2 M ≠ ⊥ → ∀ u : G, orderOf u = 2 → u ∈ centralizer (pPrimeCoreOf 2 M : Set G) → u = z

@[expose] def Prop17_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Fail17 G z k S M →
    ∀ t : G, IsConj z t → t ∈ centralizer (pPrimeCoreOf 2 M : Set G) → t = z

end CFSG.GH74.GLS.Stage2.Final.Thm4
