module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs18

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

@[expose] def Lemma18_3a : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ)
    (E : Subgroup G) (t : G), Ctx18 G z k S M p E t → ∀ X : Subgroup G,
    (∀ v ∈ Vof M E, v ∈ normalizer (X : Set G)) → ¬ X ≤ M → X ≠ ⊤ →
      ∀ J : Subgroup G, IsCompIn X J →
        Set.ncard {K : Subgroup G | IsCompIn X K} ≤ 2 ∧
          ⁅J, zpowers z⁆ = J ∧ ⁅J, omega1Z p (Op p M)⁆ = J

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
