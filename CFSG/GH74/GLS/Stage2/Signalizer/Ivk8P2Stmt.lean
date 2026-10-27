module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs18

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4

@[expose] def Lemma18_4ac : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (E : Subgroup G)
    (t : G), Ctx18 G z k S M p E t → ∀ X : Subgroup G,
    (∀ v ∈ Vof M E, v ∈ normalizer (X : Set G)) → ¬ X ≤ M → X ≠ ⊤ →
      ∀ J : Subgroup G, IsCompIn X J →
        (Em X ≤ ⁅X, zpowers z⁆ ∧ ⁅X, zpowers z⁆ ≤ Em X ⊔ (X ⊓ centralizer (Em X : Set G))) ∧
        ((E ≤ omega1Z p (Op p M) ⊔
              (centralizer (J : Set G) ⊓ (X ⊔ pPrimeCoreOf 2 (Vof M E) ⊔ zpowers z)) ∧
            (centralizer (J : Set G) ⊓ omega1Z p (Op p M)).relIndex (omega1Z p (Op p M)) = p) ∨
          (IsL34Quotient ↥J ∧ p = 3 ∧
            (centralizer (J : Set G) ⊓ (E ⊔ omega1Z p (Op p M))).relIndex
              (E ⊔ omega1Z p (Op p M)) ≤ 9 ∧ InducesUnitaryAut z J))

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
