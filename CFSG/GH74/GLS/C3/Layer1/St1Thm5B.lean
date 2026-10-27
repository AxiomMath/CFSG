module

public import CFSG.GH74.GLS.C3.Layer1.St1Prop810a

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

section MPropsB

variable {G : Type} [Group G]

structure MPropsB (A M S : Subgroup G) : Prop where
  sylow : IsSylowOf 2 S ⊤
  gammaS : gammaK 2 S (pRank 2 G) ≤ M
  gammaB : ∀ B : Subgroup G, B ≤ S → IsEStar B → gammaK 2 B 2 ≤ M
  comm_star : ∀ t ∈ M, orderOf t = 2 →
    pRank 2 ↥(centralizer ({t} : Set G) ⊓ M) = pRank 2 ↥M → t ∈ ⁅M, M⁆
  theta : ∀ B : Subgroup G, B ≤ S → IsEStar B → thetaGA B = thetaGA A

variable [Finite G]

theorem mpropsB_of_proved
    (hG : C3Hyp G) (T4 : St1Thm4 G) {A M S : Subgroup G} (hA : IsEStar A)
    (hcore : ∃ a ∈ A, a ≠ 1 ∧ pPrimeCoreOf 2 (centralizer ({a} : Set G)) ≠ ⊥) (hM : IsCoatom M)
    (hMN : normalizer (thetaGA A : Set G) ≤ M) (hS : IsSylowOf 2 S M) (hAS : A ≤ S) :
    MPropsB A M S := by
  have hr : pRank 2 G = 4 := hG.pRank_eq_four
  have hSp : IsPGroup 2 ↥S := hS.isPGroup
  exact
    { sylow := isSylowOf_top_of_theta hr T4 hS hA hAS hMN
      gammaS := gammaK_S_le_of_theta hr T4 hSp hA hAS hMN
      gammaB := fun B hBS hB => gammaK_two_le_of_theta hr T4 hSp hA hB hAS hBS hMN
      comm_star := b_iv2_8_10a G hG T4 A M S hA hcore hM hMN hS hAS
      theta := fun B hBS hB => theta_eq_of_le hr T4 hSp hA hB hAS hBS }

end MPropsB

@[expose] def B_st1_prop71_endB : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoU2Triple G → St1Thm7 G → St1Prop41 G → St1Thm4 G →
    ∀ (A M S : Subgroup G), IsEStar A →
      (∃ a ∈ A, a ≠ 1 ∧ pPrimeCoreOf 2 (centralizer ({a} : Set G)) ≠ ⊥) →
        IsCoatom M → normalizer (thetaGA A : Set G) ≤ M → IsSylowOf 2 S M → A ≤ S → MPropsB A M S →
          ∀ (x y : G) (K : Subgroup G), IsTerminallyUnbalancing x y K →
            IsSylowOf 2 (S ⊓ centralizer ({x} : Set G)) (centralizer ({x} : Set G)) → y ∈ S →
              K ≤ M → HasL2Model (kBar K) (fun q => q = 9) → pRank 2 ↥(CxK x K) = 1 → False

end CFSG.GH74.GLS
