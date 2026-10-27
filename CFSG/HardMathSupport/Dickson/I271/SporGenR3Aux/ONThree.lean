module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.A6Leaf
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.CoverCentON
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ONPair
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Cover3Sound

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier CFSG.Yardstones.Md0ec50421ce4
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

theorem center_eq_bot_of_not_hatON (hSpM : SporadicMultipliers) {X : Type} [Group X] [Finite X]
    {K B : Subgroup X} (hH : CompHyp 3 K B) (hS : I271SporType K .ONan) (hO : ¬ IsHatON ↥K) :
    Subgroup.center ↥K = ⊥ := by
  obtain ⟨e⟩ := hS
  have hZ : IsPGroup 3 (Subgroup.center ↥K) :=
    i271h_center_isPGroup Nat.prime_three hH.primeCore
  have hd := card_center_dvd_multiplier hSpM hH.quasi .ONan e
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hZ
  have hd3 : 3 ^ n ∣ 3 := by
    rw [← hn]
    exact hd
  have hn1 : n ≤ 1 := by
    by_contra h
    push Not at h
    have : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have := Nat.le_of_dvd (by norm_num) hd3
    omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn1 with h0 | h1
  · apply Subgroup.eq_bot_of_card_eq
    rw [hn, h0, pow_zero]
  · exfalso
    apply hO
    refine ⟨hH.quasi.1, ?_, ⟨e⟩⟩
    rw [hn, h1, pow_one]

section ON


theorem onThree_centShapeRk :
    CentShapeRk 3 (IsA6At 3) (RkAut 3) (NativeSporadic.Carrier .ONan) := by
  haveI : Finite (NativeSporadic.Carrier .ONan) :=
    Nat.finite_of_card_ne_zero (by
      show Nat.card NativeSporadic.ON ≠ 0
      rw [CFSG.Sporadic.ON.card_ON]; norm_num)
  obtain ⟨φ, hφ, hker, hconj, hcard⟩ := on_cover_data
  obtain ⟨E, hEn, ⟨eE⟩, hq9⟩ := alt6_normal_of_cover φ hφ hker hcard
  haveI := hEn
  have hx := shapeRkAt_alt6_of_normal E eE hq9
  intro k hk1 hkp
  have hk3 : orderOf k = 3 := orderOf_eq_prime hkp hk1
  obtain ⟨g, hg⟩ := hconj k hk3
  have h := ShapeRkAt.of_equiv Nat.prime_three
    (fun _ _ _ _ e h => ⟨h.1, ⟨e.symm.trans h.2.some⟩⟩)
    (fun _ _ _ _ e h => rkAut_of_equiv e h) (MulAut.conj g) hx
  rw [MulAut.conj_apply, ← hg] at h
  exact h

end ON

section Pair


theorem sporPair_ON_three (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers)
    (hBr : SporadicBridges) : SporPair .ONan 3 := by
  intro X _ _ hX K B hH hN hS hF hO
  right
  have hC : CompHyp 3 K B := CompHyp.of_i271Hyp hH hN.1
  have hZ : Subgroup.center ↥K = ⊥ :=
    center_eq_bot_of_not_hatON hSpM hC hS (fun h => hO ⟨h, rfl⟩)
  refine strong_of_centShapeRk (Good := IsA6At 3) (Rk := RkAut 3)
    (fun _ _ _ _ e h => ⟨h.1, ⟨e.symm.trans h.2.some⟩⟩)
    (fun _ _ _ _ e h => rkAut_of_equiv e h) hOut hBr sporadicOnePairHolds_ONan_three
    (fun Y _ _ J B' h hG hR => ?_) onThree_centShapeRk hC hN hS hZ
  obtain ⟨-, ⟨e⟩⟩ := hG
  exact strong_a6 h e (sq_le_autOrderIn_of_rkAut h.prime h.scp h.norm hR)

end Pair

end CFSG.HardMathSupport.Dickson.I271
