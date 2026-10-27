module

public import CFSG.GH74.GLS.C3.Layer1.St1Thm5B
public import CFSG.GH74.GLS.C3.Layer1.Th2P85Defs

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools

@[expose] def B_st1_prop71_lemma710 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoU2Triple G → St1Thm7 G → St1Prop41 G → St1Thm4 G →
    ∀ (A M S : Subgroup G), IsEStar A →
      (∃ a ∈ A, a ≠ 1 ∧ pPrimeCoreOf 2 (centralizer ({a} : Set G)) ≠ ⊥) →
        IsCoatom M → normalizer (thetaGA A : Set G) ≤ M → IsSylowOf 2 S M → A ≤ S → MPropsB A M S →
          ∀ (x y : G) (K : Subgroup G), IsTerminallyUnbalancing x y K →
            IsSylowOf 2 (S ⊓ centralizer ({x} : Set G)) (centralizer ({x} : Set G)) → y ∈ S →
              K ≤ M → HasL2Model (kBar K) (fun q => q = 9) → pRank 2 ↥(CxK x K) = 1 →
                ¬ (pPrimeCoreOf 2 (centralizer ({y} : Set G) ⊓ M) ⊓ centralizer ({x} : Set G) ≤
                    centralizerSection K (pPrimeCoreOf 2 K))

@[expose] def B_st1_prop71_lemma711 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Gen4 X → IsKGroupNative X → pPrimeCore 2 X = ⊥ →
    (∀ L : Subgroup X, IsSimpleSocle L ⊤ → GHList ↥L) →
      ∀ (K : Subgroup X) (x y : X), orderOf x = 2 → orderOf y = 2 → x * y = y * x →
        IsCompIn (centralizer ({x} : Set X)) K →
        HasL2Model (↥K ⧸ pPrimeCore 2 ↥K) (fun q => q = 9) →
        Th2.P85.IsTerminalSub K →
        (∀ u : X, orderOf u = 2 → (∀ k ∈ K, u * k = k * u) → u * x = x * u → u = x) →
        ¬ (pPrimeCoreOf 2 (centralizer ({y} : Set X)) ⊓ centralizer ({x} : Set X) ≤
            centralizerSection K (pPrimeCoreOf 2 K)) →
        4 ≤ pRank 2 ↥(centralizer ({x} : Set X)) →
        (pRank 2 ↥(centralizer ({x} : Set X)) = pRank 2 X → x ∈ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆) →
        K.IsSubnormal

end CFSG.GH74.GLS
