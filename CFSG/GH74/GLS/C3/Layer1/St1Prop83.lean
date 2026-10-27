module

public import CFSG.GH74.GLS.C3.Layer1.St1Prop81

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools
open CFSG.GH74.GLS.Stage1.Thm3.Sec4

@[expose] def B_st1_pumpup_eq : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → St1Thm5 G → ∀ (u z : G) (K J : Subgroup G),
    IsStar2 u → IsStar2 z → IsIL2Pair u K → z ∈ CxK u K → PumpUpLT 2 u K z J →
      IsTrivialPumpupAt u K z → J = K

section Prop83

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElementaryAbelian_zpowers_of_orderOf_two {z : G} (hz : orderOf z = 2) :
    CFSG.IsElementaryAbelian 2 ↥(zpowers z) := by
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  exact
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun w => by
        obtain ⟨w, k, rfl⟩ := w
        apply Subtype.ext
        show (z ^ k) ^ 2 = 1
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow] }

theorem prop83_of_leaves
    (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) (hpe : B_st1_pumpup_eq) (hG : C3Hyp G) (hN : NoU2Triple G)
    (P41 : St1Prop41 G) (P51 : St1Prop51 G) (T5 : St1Thm5 G) {x : G} {S U : Subgroup G} {u : G}
    {K W : Subgroup G} (hc : Config8 x S U u K W) :
    HasL2Model (kBar K) (fun q => q = 9) ∧ pRank 2 ↥(W ⊓ CxK u K) = 1 := by
  have hU : IsNormalFourOf S U := ⟨hc.four, hc.U_le, hc.U_normal⟩
  have hstar : IsStar2 u := isStar2_of_mem_normalFour hc.sylow_S hU hc.u_mem.1 hc.u_mem.2
  obtain ⟨-, -, z, J, hpump, htriv, hterm, hzW, hzcent, hzC, hzstar⟩ :=
    P51 u x K W hc.unbal hstar hc.sylow_W hc.x_mem_W
  obtain ⟨-, -, hL29J, hh⟩ := terminallyUnbalancing_L29 h102 h14 hL34 hadd hG hN P41 hterm
  have hJK : J = K := hpe G hG T5 u z K J hstar hzstar hc.unbal.1 hzC hpump htriv
  obtain ⟨-, ⟨e⟩⟩ := htriv J hpump
  refine ⟨TwoThin.hasL2Model_of_mulEquiv e hL29J, le_antisymm ?_ ?_⟩
  ·
    have hQ : W ⊓ CxK u K ≤ CxK z J := by
      rw [hJK]
      intro q hq
      exact ⟨mem_centralizer_singleton_iff.mpr (hzcent q hq.1).symm, hq.2.2⟩
    calc pRank 2 ↥(W ⊓ CxK u K) ≤ pRank 2 ↥(CxK z J) := Bg.pRank_subgroup_mono one_lt_two hQ
      _ = 1 := hh
  ·
    refine le_pRank_of_elem (H := W ⊓ CxK u K) (B := zpowers z)
      (zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hzW, hzC⟩))
      (isElementaryAbelian_zpowers_of_orderOf_two hzstar.1) (k := 1) ?_
    rw [Nat.card_zpowers, hzstar.1, pow_one]

theorem b_st1_prop83_of_leaves
    (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) (hpe : B_st1_pumpup_eq) : B_st1_prop83 :=
  fun _ _ _ hG hN _ P41 P51 T5 _ _ _ _ _ _ hc =>
    prop83_of_leaves h102 h14 hL34 hadd hpe hG hN P41 P51 T5 hc

end Prop83

end CFSG.GH74.GLS
