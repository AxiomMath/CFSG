module

public import CFSG.GH74.GLS.C3.Layer1.St1Thm5B
public import CFSG.GH74.GLS.C3.Layer1.St1EndZ

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools

@[expose] def B_st1_prop71_endN : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoU2Triple G → St1Thm7 G → St1Prop41 G → St1Thm4 G →
    ∀ (A M S : Subgroup G), IsEStar A →
      (∃ a ∈ A, a ≠ 1 ∧ pPrimeCoreOf 2 (centralizer ({a} : Set G)) ≠ ⊥) →
        IsCoatom M → normalizer (thetaGA A : Set G) ≤ M → IsSylowOf 2 S M → A ≤ S → MPropsB A M S →
          ∀ (x y : G) (K : Subgroup G), IsTerminallyUnbalancing x y K →
            IsSylowOf 2 (S ⊓ centralizer ({x} : Set G)) (centralizer ({x} : Set G)) → y ∈ S →
              K ≤ M → HasL2Model (kBar K) (fun q => q = 9) → pRank 2 ↥(CxK x K) = 1 →
                (∃ s ∈ S, x * s ≠ s * x) → False

theorem b_st1_prop71_endB_of_endN
    (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) (hN : B_st1_prop71_endN) : B_st1_prop71_endB := by
  intro G _ _ hG hNoU T7 P41 T4 A M S hA hcore hM hMN hS hAS hMP x y K hxyK hT hy hKM hL29 h1
  by_cases hc : ∀ s ∈ S, x * s = s * x
  · obtain ⟨hstar, -, -, -⟩ := terminallyUnbalancing_L29 h102 h14 hL34 hadd hG hNoU P41 hxyK
    have hx2 : orderOf x = 2 := hstar.1
    have hxS : x ∈ S := by
      refine (C3.Layer1.Iv251.mem_of_isSylowOf_of_central hT (mem_centralizer_singleton_iff.2 rfl) hx2
        (fun c hc' => (mem_centralizer_singleton_iff.1 hc').symm) : x ∈ S ⊓ centralizer ({x} : Set G)).1
    let P : Sylow 2 G := Sylow.ofCard S (by rw [hMP.sylow.card_eq, Subgroup.card_top])
    have hPS : (P : Subgroup G) = S := Sylow.coe_ofCard _ _
    have hcen : IsCentralInvolution x :=
      ⟨hx2, P, by rw [hPS]; exact hxS, fun s hs => by rw [hPS] at hs; exact (hc s hs).symm⟩
    exact C3.Layer1.EndZ.endB_of_central hG hstar hcen hxyK.unbalancing.1.2 hL29 h1
  · push Not at hc
    exact hN G hG hNoU T7 P41 T4 A M S hA hcore hM hMN hS hAS hMP x y K hxyK hT hy hKM hL29 h1 hc

end CFSG.GH74.GLS
