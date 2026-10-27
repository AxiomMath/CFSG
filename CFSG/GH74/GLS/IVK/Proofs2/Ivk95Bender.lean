module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95Ord
public import CFSG.GH74.KGroups.CoverEven
public import CFSG.GH74.KGroups.Sz8

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
open CFSG.GH74.Uniqueness.Bender

theorem bender_card_centralizer_involution {K : Type} [Group K]
    [Finite K] {n i e : ℕ} (h : BenderType K n i e) {y : K} (hy : y * y = 1) (hy1 : y ≠ 1) :
    Nat.card ↥(centralizer ({y} : Set K)) = (2 ^ n) ^ i * e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hy) hy1
  have hz : IsPGroup 2 (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have hyQ : y ∈ (Q : Subgroup K) := hQ (mem_zpowers y)
  have hyroot : y ∈ rootCenter (Q : Subgroup K) := hc.mem_rootCenter_of_mul_self hyQ hy
  exact hc.card_centralizer hyroot hy1

theorem ivk95_l28 :
    Ivk95Empty (fun X _ => LieModel X .PSL 2 2 3) := by
  refine ivk95_empty_of_cfg fun J _ _ hJ z hz => ?_
  obtain ⟨e⟩ := KGroups.equiv_psl2_of_lieModel_even (S := J) (f := 3) (by norm_num) hJ
  have hB : BenderType J 3 1 1 := .linear 3 (by norm_num) e
  have hcard := bender_card_centralizer_involution hB hz.mul_self_eq_one hz.ne_one
  exact hz.false_of_card_cent_dvd (N := 8) (by rw [hcard]; norm_num)
    (not_sl2_dvd_of_lt (by norm_num) (by norm_num))

theorem ivk95_l216 :
    Ivk95Empty (fun X _ => LieModel X .PSL 2 2 4) := by
  refine ivk95_empty_of_cfg fun J _ _ hJ z hz => ?_
  obtain ⟨e⟩ := KGroups.equiv_psl2_of_lieModel_even (S := J) (f := 4) (by norm_num) hJ
  have hB : BenderType J 4 1 1 := .linear 4 (by norm_num) e
  have hcard := bender_card_centralizer_involution hB hz.mul_self_eq_one hz.ne_one
  exact hz.false_of_card_cent_dvd (N := 16) (by rw [hcard]; norm_num)
    (not_sl2_dvd_of_lt (by norm_num) (by norm_num))

theorem ivk95_u34 :
    Ivk95Empty (fun X _ => LieModel X .PSU 3 2 2) := by
  refine ivk95_empty_of_cfg fun J _ _ hJ z hz => ?_
  have hS := CFSG.GH74.Generic.stated_of_lieModel_PSU hJ
  obtain ⟨e⟩ := (RankTwoShapes.statedClassicalModel_PSU_three_two_iff J 2 le_rfl).1 hS
  have hB : BenderType J 2 3 _ := .unitary 2 le_rfl e
  have hcard := bender_card_centralizer_involution hB hz.mul_self_eq_one hz.ne_one
  have h320 : Nat.card ↥(centralizer ({z} : Set J)) = 320 := by
    rw [hcard]
    norm_num
  exact hz.false_of_card_cent_dvd (N := 320) (by rw [h320])
    (fun q _ => not_sl2_dvd_of_not_three (by norm_num) q)

theorem ivk95_sz8 :
    Ivk95Empty (fun X _ => LieModel X .twistedB2 0 2 3) := by
  refine ivk95_empty_of_cfg fun J _ _ hJ z hz => ?_
  obtain ⟨e⟩ := KGroups.Sz8.equiv_of_lieModel hJ
  have hcard : Nat.card J = 29120 := by
    rw [Nat.card_congr e.toEquiv, KGroups.card_group KGroups.Sz8.QP KGroups.Sz8.QP_ok,
      KGroups.Sz8.QP_valid.2]
  exact hz.false_of_card_group (N := 29120) (by rw [hcard])
    (fun q _ => not_sl2_dvd_of_not_three (by norm_num) q)

end CFSG.GH74.GLS.IVK.Proofs2
