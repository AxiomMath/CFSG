module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.St1Thm7

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement

section Rank4

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem IsIL2Pair.x_mem_CxK {x : G} {K : Subgroup G} (h : IsIL2Pair x K) : x ∈ CxK x K := by
  have hc : ∀ k ∈ K, x * k = k * x := fun k hk =>
    (mem_centralizer_singleton_iff.mp (h.2.1 hk)).symm
  refine ⟨mem_centralizer_singleton_iff.mpr rfl, ?_⟩
  have hcK : x ∈ centralizer (K : Set G) := Subgroup.mem_centralizer_iff.2 fun k hk => (hc k hk).symm
  have hnK : x ∈ normalizer (K : Set G) := Subgroup.centralizer_le_normalizer _ hcK
  refine ⟨hnK, ?_, fun k hk => ?_⟩
  · have hcM : x ∈ centralizer ((pPrimeCoreOf 2 K : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun m hm => (hc m (pPrimeCoreOf_le_self K hm)).symm
    exact Subgroup.centralizer_le_normalizer _ hcM
  · have : ⁅k, x⁆ = 1 := by
      rw [commutatorElement_def]
      calc k * x * k⁻¹ * x⁻¹ = (x * k) * k⁻¹ * x⁻¹ := by rw [← hc k hk]
        _ = 1 := by group
    rw [this]
    exact one_mem _

theorem isTwoTerminal_of_terminallyUnbalancing (hG : C3Hyp G) (P41 : St1Prop41 G) {x y : G}
    {K : Subgroup G} (h : IsTerminallyUnbalancing x y K) : IsTwoTerminal x K := by
  by_contra hnt
  have h5 := P41.2 x y K ⟨⟨h.unbalancing, h.trivialPumpups⟩, hnt, h.sylow⟩
  have := hG.pRank_eq_four
  omega

theorem terminallyUnbalancing_L29
    (h102 : B_ivk_10_2) (h14 : B_prop14) (hL34 : B_gen4_noL34_elem)
    (hadd : B_ivk_rank_add_L29) (hG : C3Hyp G) (hN : NoU2Triple G) (P41 : St1Prop41 G) {x y : G}
    {K : Subgroup G} (h : IsTerminallyUnbalancing x y K) :
    IsStar2 x ∧ IsTwoTerminal x K ∧ HasL2Model (kBar K) (fun q => q = 9) ∧
      pRank 2 ↥(CxK x K) = 1 := by
  have hr4 : pRank 2 G = 4 := hG.pRank_eq_four
  have hu : IsUnbalancingTriple x y K := h.unbalancing
  have hpair : IsIL2Pair x K := hu.1
  have hU2 : InU2 (kBar K) := h102 G hG x y K hu.isLocallyUnbalancing
  have h4 := h14 G hG x K hpair hU2
  have hstar : IsStar2 x :=
    ⟨hpair.1, le_antisymm (Bg.pRank_subgroup_le one_lt_two _) (by rw [hr4]; exact h4)⟩
  have hterm : IsTwoTerminal x K := isTwoTerminal_of_terminallyUnbalancing hG P41 h
  have hd : IsL34Quotient (kBar K) → False := fun hl34 =>
    hL34 G hG.gen4 x K hpair.1 hpair.2 ⟨hl34, (inU2_center hU2).1, (inU2_center hU2).2⟩
  by_cases hL29 : HasL2Model (kBar K) (fun q => q = 9)
  · refine ⟨hstar, hterm, hL29, ?_⟩
    have hle : pRank 2 ↥(CxK x K) + 2 ≤ pRank 2 G := hadd G hG x K hpair hL29
    have hge : 1 ≤ pRank 2 ↥(CxK x K) := by
      refine le_pRank_of_elem (B := zpowers x) (zpowers_le.mpr hpair.x_mem_CxK) ?_ (k := 1) ?_
      · have hx2 : x ^ 2 = 1 := by rw [← hpair.1]; exact pow_orderOf_eq_one x
        exact
          { toIsMulCommutative := inferInstance
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun z => by
              obtain ⟨z, k, rfl⟩ := z
              apply Subtype.ext
              show (x ^ k) ^ 2 = 1
              rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow] }
      · rw [Nat.card_zpowers, hpair.1, pow_one]
    by_contra hne
    have h2 : 2 ≤ pRank 2 ↥(CxK x K) := by omega
    apply hN
    refine ⟨x, y, K, hu.isLocallyUnbalancing, hterm, hstar, fun hl34 => (hd hl34).elim, fun _ => ?_⟩
    exact ⟨h2, Or.inr (by omega)⟩
  · exfalso
    apply hN
    exact ⟨x, y, K, hu.isLocallyUnbalancing, hterm, hstar, fun hl34 => (hd hl34).elim,
      fun hl29 => (hL29 hl29).elim⟩

end Rank4

section Small

variable {G : Type} [Group G]

theorem pPrimeCoreOf_ne_bot_of_ne_bot {C : Subgroup G} (h : pPrimeCore 2 ↥C ≠ ⊥) :
    pPrimeCoreOf 2 C ≠ ⊥ := by
  intro hbot
  apply h
  unfold pPrimeCoreOf at hbot
  exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp hbot

end Small

end CFSG.GH74.GLS
