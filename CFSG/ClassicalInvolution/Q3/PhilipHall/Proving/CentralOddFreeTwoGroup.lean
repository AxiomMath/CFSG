module

public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs
public import CFSG.Open.GeneralizedFittingSelfCentralizingMilestoneDefs

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Proving

open CFSG.Open

theorem eq_bot_of_normal_odd_of_classicalInvolutionOddCore_eq_bot {Y : Type} [Group Y]
    (hO : classicalInvolutionOddCore Y = ⊥) {N : Subgroup Y} (hN : N.Normal)
    (ho : Odd (Nat.card N)) : N = ⊥ := by
  have hle : N ≤ classicalInvolutionOddCore Y :=
    le_sSup (s := {N : Subgroup Y | N.Normal ∧ Odd (Nat.card N)}) ⟨hN, ho⟩
  rw [hO, le_bot_iff] at hle
  exact hle

theorem eq_one_of_central_odd_of_classicalInvolutionOddCore_eq_bot {Y : Type} [Group Y]
    (hO : classicalInvolutionOddCore Y = ⊥) {z : Y} (hz : z ∈ Subgroup.center Y)
    (ho : Odd (orderOf z)) : z = 1 := by
  have hN : (Subgroup.zpowers z).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute g z := Subgroup.mem_center_iff.mp hz g
    have hk : g * z ^ k = z ^ k * g := (hc.zpow_right k).eq
    rw [hk, mul_assoc, mul_inv_cancel, mul_one]
    exact zpow_mem (Subgroup.mem_zpowers z) k
  have h1 : Subgroup.zpowers z = ⊥ :=
    eq_bot_of_normal_odd_of_classicalInvolutionOddCore_eq_bot hO hN (by
      rw [Nat.card_zpowers]; exact ho)
  have h2 : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
  rw [h1] at h2
  exact Subgroup.mem_bot.mp h2

theorem isPGroup_two_of_le_center_of_classicalInvolutionOddCore_eq_bot {Y : Type} [Group Y]
    [Finite Y] (hO : classicalInvolutionOddCore Y = ⊥) {F : Subgroup Y}
    (hF : F ≤ Subgroup.center Y) : IsPGroup 2 F := by
  intro g
  have hx : (g : Y) ∈ Subgroup.center Y := hF g.2
  have hne : orderOf (g : Y) ≠ 0 := (orderOf_pos (g : Y)).ne'
  obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hne
  have hy : (g : Y) ^ (2 ^ k) ∈ Subgroup.center Y := Subgroup.pow_mem _ hx _
  have hym : ((g : Y) ^ (2 ^ k)) ^ m = 1 := by
    rw [← pow_mul, ← hnm, pow_orderOf_eq_one]
  have hodd : Odd (orderOf ((g : Y) ^ (2 ^ k))) :=
    Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hym)
  have h1 := eq_one_of_central_odd_of_classicalInvolutionOddCore_eq_bot hO hy hodd
  refine ⟨k, Subtype.ext ?_⟩
  simpa using h1

theorem isPGroup_two_genFittingFitting {Y : Type} [Group Y] [Finite Y]
    (hO : classicalInvolutionOddCore Y = ⊥) (hF : genFittingFitting Y ≤ Subgroup.center Y) :
    IsPGroup 2 (genFittingFitting Y) :=
  isPGroup_two_of_le_center_of_classicalInvolutionOddCore_eq_bot hO hF

theorem genFittingFitting_ne_bot_of_not_le {Y : Type} [Group Y] {L : Subgroup Y}
    (h : ¬ genFittingFitting Y ≤ L) : genFittingFitting Y ≠ ⊥ := by
  intro hb
  apply h
  rw [hb]
  exact bot_le

end CFSG.ClassicalInvolution.Q3.PhilipHall.Proving

end
