module

public import CFSG.Dihedral.OriginalInvolutions
public import CFSG.Dihedral.OriginalOddCore

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem centralizer_R_quotient_card : Nat.card (d.C ⧸ d.R.subgroupOf d.C) = 2 ^ d.n := by
  let : (d.R.subgroupOf d.C).Normal := d.R_normal
  have hcard : Nat.card (d.R.subgroupOf d.C) = Nat.card d.R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe d.R_le).toEquiv
  have h := (d.R.subgroupOf d.C).card_eq_card_quotient_mul_card_subgroup
  rw [d.centralizer_card, hcard, mul_comm (Nat.card d.R)] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := d.R)) h.symm

theorem centralizer_R_two_quotient :
    letI : (d.R.subgroupOf d.C).Normal := d.R_normal
    IsPGroup 2 (d.C ⧸ d.R.subgroupOf d.C) := by
  let : (d.R.subgroupOf d.C).Normal := d.R_normal
  exact IsPGroup.of_card d.centralizer_R_quotient_card

theorem odd_subgroup_le_R_of_le_C (W : Subgroup G) (hWC : W ≤ d.C)
    (hodd : Odd (Nat.card W)) : W ≤ d.R := by
  let : (d.R.subgroupOf d.C).Normal := d.R_normal
  have h := odd_le_normal_of_two_quotient W d.C hWC (d.R.subgroupOf d.C)
    hodd d.centralizer_R_two_quotient
  rwa [Subgroup.map_subgroupOf_eq_of_le d.R_le] at h

theorem centralizer_oddCore_eq_R : oddCoreOf d.C = d.R := by
  exact le_antisymm (d.odd_subgroup_le_R_of_le_C _ (oddCoreOf_le d.C) (oddCoreOf_odd d.C))
    (normal_odd_le_oddCoreOf d.R d.C d.R_le d.R_normal d.R_odd)

theorem centralizer_oddCore_two_quotient : IsPGroup 2 (d.C ⧸ Assembly.oddCore d.C) := by
  have hcard : Nat.card (Assembly.oddCore d.C) = Nat.card d.R := by
    have h := congrArg (fun U : Subgroup G => Nat.card U) d.centralizer_oddCore_eq_R
    rwa [oddCoreOf, Subgroup.card_map_of_injective d.C.subtype_injective] at h
  have h := (Assembly.oddCore d.C).card_eq_card_quotient_mul_card_subgroup
  rw [d.centralizer_card, hcard, mul_comm (Nat.card d.R)] at h
  exact IsPGroup.of_card (Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := d.R)) h.symm)

theorem centralizer_hasNormalTwoComplement : HasNormalTwoComplement d.C := by
  refine ⟨d.R, d.R_le, d.R_normal, d.R_odd, d.n, ?_⟩
  rw [Subgroup.index_eq_card]
  exact d.centralizer_R_quotient_card

end CFSG.DihedralBlueprint.OriginalData
