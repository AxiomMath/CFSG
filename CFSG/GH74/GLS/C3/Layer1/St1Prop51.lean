module

public import CFSG.GH74.GLS.C3.Layer1.St1Thm5
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.GH74.GLS.C3.Layer1.St1Theta

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

@[expose] def B_st1_prop51_pumpup : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → NoU2Triple G → St1Thm7 G → St1Prop41 G →
    ∀ (x y : G) (K R : Subgroup G), IsUnbalancingTriple x y K → IsStar2 x →
      IsSylowOf 2 R (NxK x K) → y ∈ R →
        ∃ (z : G) (J : Subgroup G), PumpUpLT 2 x K z J ∧ IsTrivialPumpupAt x K z ∧
          IsTerminallyUnbalancing z y J ∧ z ∈ R ∧ (∀ r ∈ R, z * r = r * z) ∧ z ∈ CxK x K ∧
          IsStar2 z

section Prop51

variable {G : Type} [Group G] [Finite G]

theorem pRank_eq_of_isSylowOf {R N : Subgroup G} (h : IsSylowOf 2 R N) :
    pRank 2 ↥R = pRank 2 ↥N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := h.exists_sylow_eq_subgroupOf
  have h1 := (CFSG.SectionRank.pRank_sylow Q).2
  rw [hQ] at h1
  have e : ↥(R.subgroupOf N) ≃* ↥R := (Subgroup.subgroupOfEquivOfLe h.le)
  rw [← Bg.pRank_mulEquiv one_lt_two e]
  exact h1

theorem prop51_of_leaves
    (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) (h47 : B_iv2_4_7) (hpu : B_st1_prop51_pumpup)
    (hG : C3Hyp G) (hN : NoU2Triple G) (T7 : St1Thm7 G) (P41 : St1Prop41 G) : St1Prop51 G := by
  intro x y K R hu hstar hR hyR
  have hr4 : pRank 2 G = 4 := hG.pRank_eq_four
  obtain ⟨z, J, hpump, htriv, hterm, hzR, hzcent, hzC, hzstar⟩ :=
    hpu G hG hN T7 P41 x y K R hu hstar hR hyR
  have hU2 : InU2 (kBar K) := h102 G hG x y K hu.isLocallyUnbalancing
  obtain ⟨A, hA, hxA⟩ := exists_isEStar_of_isStar2 hstar
  have hAC : A ≤ centralizer ({x} : Set G) := fun c hc =>
    mem_centralizer_singleton_iff.mpr (hA.commute hc hxA)
  have hAN : A ≤ NxK x K := le_inf hAC (h47 G hG x K hu.1 hU2 A hA hxA)
  have hge : 4 ≤ pRank 2 ↥(NxK x K) :=
    le_pRank_of_elem hAN hA.1 (k := 4) (by rw [hA.2, hr4])
  have hrank : pRank 2 ↥R = pRank 2 G := by
    refine le_antisymm (Bg.pRank_subgroup_le one_lt_two R) ?_
    rw [pRank_eq_of_isSylowOf hR, hr4]
    exact hge
  obtain ⟨-, -, hL29J, -⟩ := terminallyUnbalancing_L29 h102 h14 hL34 hadd hG hN P41 hterm
  obtain ⟨-, ⟨e⟩⟩ := htriv J hpump
  exact ⟨hrank, Or.inl (TwoThin.hasL2Model_of_mulEquiv e hL29J), z, J, hpump, htriv, hterm, hzR,
    hzcent, hzC, hzstar⟩

theorem b_st1_prop51_of_leaves
    (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) (h47 : B_iv2_4_7) (hpu : B_st1_prop51_pumpup) : B_st1_prop51 :=
  fun _ _ _ hG hN T7 P41 => prop51_of_leaves h102 h14 hL34 hadd h47 hpu hG hN T7 P41

end Prop51

end CFSG.GH74.GLS
