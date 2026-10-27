module

public import CFSG.GH74.GLS.C3.Layer1.St1P77L29

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

@[expose] def B_iv2_8_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G →
    (∃ t : G, orderOf t = 2 ∧ pPrimeCore 2 ↥(centralizer ({t} : Set G)) ≠ ⊥) →
      ∃ a x : G, orderOf a = 2 ∧ orderOf x = 2 ∧ a * x = x * a ∧
        ¬ pPrimeCoreOf 2 (centralizer ({x} : Set G)) ⊓ centralizer ({a} : Set G) ≤
          pPrimeCoreOf 2 (centralizer ({a} : Set G))

section Thm5C

variable {G : Type} [Group G] [Finite G]

theorem thm5_of_leavesC
        (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) (h47 : B_iv2_4_7) (h61 : B_ivk_6_1_L29) (h75 : B_st1_lemma75)
    (h85 : B_iv2_8_5) (hpu : B_st1_prop51_pumpup) (hend : B_st1_prop71_endB) (hG : C3Hyp G)
    (hN : NoU2Triple G) (T7 : St1Thm7 G) (P41 : St1Prop41 G) (T4 : St1Thm4 G) : St1Thm5 G := by
  intro t ht
  by_contra hne
  have hr4 : pRank 2 G = 4 := hG.pRank_eq_four
  have ht1 : t ≠ 1 := fun h => by
    have := ht.1
    rw [h, orderOf_one] at this
    omega
  obtain ⟨A, hA, htA⟩ := exists_isEStar_of_isStar2 ht
  have hne' : pPrimeCoreOf 2 (centralizer ({t} : Set G)) ≠ ⊥ := pPrimeCoreOf_ne_bot_of_ne_bot hne
  obtain ⟨M, S, hM, hMN, hS, hAS⟩ := exists_config_of_thetaGA hG.kproper.1 hA (by omega) (T4 A hA)
    htA ht1 hne'
  have hcore : ∃ a ∈ A, a ≠ 1 ∧ pPrimeCoreOf 2 (centralizer ({a} : Set G)) ≠ ⊥ :=
    ⟨t, htA, ht1, hne'⟩
  have hMP : MPropsB A M S := mpropsB_of_proved hG T4 hA hcore hM hMN hS hAS
  obtain ⟨a, x0, ha, hx0, hax0, hnot⟩ := h85 G hG ⟨t, ht.1, hne⟩
  obtain ⟨K0, hu0⟩ := exists_isUnbalancingTriple_of_not_le ha hx0 hax0 hnot
  have hU2 : InU2 (kBar K0) := h102 G hG a x0 K0 hu0.isLocallyUnbalancing
  have hstar : IsStar2 a :=
    ⟨hu0.1.1, le_antisymm (Bg.pRank_subgroup_le one_lt_two _)
      (by rw [hr4]; exact h14 G hG a K0 hu0.1 hU2)⟩
  have hxN : x0 ∈ NxK a K0 := ⟨hu0.2.2.1, hu0.2.2.2.1⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxp : IsPGroup 2 ↥(zpowers x0) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hu0.2.1]; norm_num)
  obtain ⟨R, hR, hxR⟩ := exists_isSylowOf_ge (zpowers_le.2 hxN) hxp
  obtain ⟨z, J, -, -, hxyK, -⟩ := hpu G hG hN T7 P41 a x0 K0 R hu0 hstar hR (hxR (mem_zpowers x0))
  obtain ⟨g, hxyK', hT', hy'⟩ := h75 G S hMP.sylow z x0 J hxyK
  have hKM := prop77_rank4B' h102 h14 hL34 hadd h47 h61 hG hN P41 hMN hMP hxyK' hT'
  obtain ⟨-, -, hL29, h1⟩ := terminallyUnbalancing_L29 h102 h14 hL34 hadd hG hN P41 hxyK'
  exact hend G hG hN T7 P41 T4 A M S hA hcore hM hMN hS hAS hMP _ _ _ hxyK' hT' hy' hKM hL29 h1

theorem b_st1_thm5_of_leavesC
        (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) (h47 : B_iv2_4_7) (h61 : B_ivk_6_1_L29) (h75 : B_st1_lemma75)
    (h85 : B_iv2_8_5) (hpu : B_st1_prop51_pumpup) (hend : B_st1_prop71_endB) : B_st1_thm5 :=
  fun _ _ _ hG hN T7 P41 T4 =>
    thm5_of_leavesC h102 h14 hL34 hadd h47 h61 h75 h85 hpu hend hG hN T7 P41 T4

end Thm5C

end CFSG.GH74.GLS
