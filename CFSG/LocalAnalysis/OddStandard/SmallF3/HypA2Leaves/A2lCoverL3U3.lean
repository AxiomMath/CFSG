module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCoverStated

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem a2l_false_psl33 {K : Type} [Group K] [Finite K] (hq : IsQuasisimple K)
    (h2 : IsPGroup 2 ↥(center K)) (hZ : center K ≠ ⊥)
    (hm : LieModel (K ⧸ center K) .PSL 3 3 1) : False := by
  haveI : Group.IsPerfect K := hq.1
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  haveI := Fintype.ofFinite F
  have hF : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card, hcard]; norm_num
  have hk : ringChar F ≠ 2 := a2l_ringChar_ne_two (by rw [hF]; decide)
  exact hZ (a2l_center_eq_bot_of_cover (a2l_splits_statedSL hk (by norm_num)) h2 _ e
    (a2l_scalars_sl_three_eq_bot hF))

theorem a2l_false_psu33 {K : Type} [Group K] [Finite K] (hq : IsQuasisimple K)
    (h2 : IsPGroup 2 ↥(center K)) (hZ : center K ≠ ⊥)
    (hm : LieModel (K ⧸ center K) .PSU 3 3 1) : False := by
  haveI : Group.IsPerfect K := hq.1
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  have hd := a2l_unitaryFieldData_three hcard
  haveI := hd.finite
  haveI := hd.charP
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF9 : Nat.card F = 9 := by rw [hcard]; norm_num
  exact hZ (a2l_center_eq_bot_of_cover (a2l_splits_statedSU hcard (by norm_num) (by norm_num))
    h2 _ e (a2l_scalars_su_three_eq_bot hF9))

end CFSG.OddStandard.SmallF3.HypA2Leaves
