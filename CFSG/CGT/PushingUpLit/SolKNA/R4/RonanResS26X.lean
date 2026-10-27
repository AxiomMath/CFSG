module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.TripleBalance
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3

section Central

variable {X : Type} [Group X] [Finite X]

theorem central_odd_eq_one (hO : classicalInvolutionOddCore X = ⊥) {w : X}
    (hw : w ∈ Subgroup.center X) (hodd : Odd (orderOf w)) : w = 1 := by
  have hN : (Subgroup.zpowers w).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hxC : x ∈ Subgroup.center X := Subgroup.zpowers_le.mpr hw hx
    have e : g * x * g⁻¹ = x := by
      rw [Subgroup.mem_center_iff.mp hxC g]
      group
    rw [e]
    exact hx
  have hcard : Odd (Nat.card (Subgroup.zpowers w)) := by
    rw [Nat.card_zpowers]
    exact hodd
  have hle : Subgroup.zpowers w ≤ CFSG.Open.classicalInvolutionOddCore X :=
    le_sSup (show Subgroup.zpowers w ∈ {N : Subgroup X | N.Normal ∧ Odd (Nat.card N)} from
      ⟨hN, hcard⟩)
  rw [hO] at hle
  exact Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers w))

theorem inf_center_eq_bot_of_unique_involution (hO : classicalInvolutionOddCore X = ⊥)
    {K : Subgroup X} {z : X} (hU : IsUniqueInvolution K z) (hzc : z ∉ Subgroup.center X) :
    ∀ w : X, w ∈ K → w ∈ Subgroup.center X → w = 1 := by
  intro w hwK hwC
  refine central_odd_eq_one hO hwC ?_
  rcases Nat.even_or_odd (orderOf w) with ⟨m, hm⟩ | ho
  · exfalso
    have hmpos : 0 < m := by
      have := orderOf_pos w
      omega
    have hv2 : w ^ m * w ^ m = 1 := by
      rw [← pow_add, ← hm, pow_orderOf_eq_one]
    have hv1 : w ^ m ≠ 1 := by
      intro h1
      have h2 := Nat.le_of_dvd hmpos (orderOf_dvd_of_pow_eq_one h1)
      omega
    have hvz : w ^ m = z := (hU.unique (w ^ m) (Subgroup.pow_mem _ hwK m) hv2).resolve_left hv1
    exact hzc (by rw [← hvz]; exact Subgroup.pow_mem _ hwC m)
  · exact ho

end Central

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
