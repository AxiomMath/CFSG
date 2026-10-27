module

public import CFSG.GH74.GLS.C3.Layer1.St1Thm5B

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

@[expose] def B_ivk_6_1_L29 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K : Subgroup G), IsIL2Pair x K →
    HasL2Model (kBar K) (fun q => q = 9) → pRank 2 ↥(CxK x K) = 1 →
      ∀ A : Subgroup G, A ≤ NxK x K → CFSG.IsElementaryAbelian 2 ↥A → Nat.card ↥A = 2 ^ 4 → x ∈ A →
        K ≤ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊔ gammaK 2 A (4 - 2)

section Prop77L29

variable {G : Type} [Group G] [Finite G]

theorem prop77_rank4B'
    (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) (h47 : B_iv2_4_7) (h61 : B_ivk_6_1_L29) (hG : C3Hyp G) (hN : NoU2Triple G)
    (P41 : St1Prop41 G) {A M S : Subgroup G} (hMN : normalizer (thetaGA A : Set G) ≤ M)
    (hMP : MPropsB A M S) {x y : G} {K : Subgroup G} (h : IsTerminallyUnbalancing x y K)
    (hT : IsSylowOf 2 (S ⊓ centralizer ({x} : Set G)) (centralizer ({x} : Set G))) : K ≤ M := by
  obtain ⟨hstar, -, hL29, hrank1⟩ := terminallyUnbalancing_L29 h102 h14 hL34 hadd hG hN P41 h
  have hpair : IsIL2Pair x K := h.unbalancing.1
  have hr4 : pRank 2 G = 4 := hG.pRank_eq_four
  have hx1 : x ≠ 1 := fun h1 => by
    have := hstar.1
    rw [h1, orderOf_one] at this
    omega
  have hTrank : pRank 2 ↥(S ⊓ centralizer ({x} : Set G)) = pRank 2 G := by
    rw [pRank_eq_of_isSylowOf hT]
    exact hstar.2
  obtain ⟨A', hA'T, hA'⟩ := exists_isEStar_le hTrank
  have hA'S : A' ≤ S := hA'T.trans inf_le_left
  have hA'C : A' ≤ centralizer ({x} : Set G) := hA'T.trans inf_le_right
  have hxA' : x ∈ A' := hA'.mem_of_commute hstar.1 fun a ha =>
    (mem_centralizer_singleton_iff.mp (hA'C ha)).symm
  have hV : pPrimeCoreOf 2 (centralizer ({x} : Set G)) ≤ M :=
    (pPrimeCoreOf_le_thetaGA hxA' hx1).trans
      ((hMP.theta A' hA'S hA').le.trans (Subgroup.le_normalizer.trans hMN))
  have hΓ : gammaK 2 A' 2 ≤ M := hMP.gammaB A' hA'S hA'
  have hcard : Nat.card ↥A' = 2 ^ 4 := by rw [hA'.2, hr4]
  have hU2 : InU2 (kBar K) := h102 G hG x y K h.unbalancing.isLocallyUnbalancing
  have hA'N : A' ≤ NxK x K := le_inf hA'C (h47 G hG x K hpair hU2 A' hA' hxA')
  exact (h61 G hG x K hpair hL29 hrank1 A' hA'N hA'.1 hcard hxA').trans (sup_le hV hΓ)

end Prop77L29

end CFSG.GH74.GLS
