module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddCentralSylowLifting

public section

namespace CFSG.ProperTwoGeneratedCore

variable {K : Type*} [Group K]

theorem sylow_restriction_same_ambient_image
    (p : ℕ) (B Y : Subgroup K) (hYB : Y ≤ B) (P : Sylow p B)
    (hPY : (P : Subgroup B).map B.subtype ≤ Y) :
    ∃ R : Sylow p Y,
      (R : Subgroup Y).map Y.subtype = (P : Subgroup B).map B.subtype := by
  let f := Subgroup.inclusion hYB
  have hrange : (P : Subgroup B) ≤ f.range := by
    rw [Subgroup.inclusion_range]
    intro a ha
    exact hPY (Subgroup.mem_map_of_mem B.subtype ha)
  let R := P.comapOfInjective f (Subgroup.inclusion_injective hYB) hrange
  have hmap : (R : Subgroup Y).map f = (P : Subgroup B) := by
    rw [Sylow.coe_comapOfInjective, Subgroup.map_comap_eq_self hrange]
  refine ⟨R, ?_⟩
  have h := congrArg (Subgroup.map B.subtype) hmap
  rw [Subgroup.map_map] at h
  have hcomp : B.subtype.comp f = Y.subtype := by ext a; rfl
  rwa [hcomp] at h

theorem sylow_extension_same_ambient_image [Finite K]
    (p : ℕ) (hp : p.Prime) (B Y : Subgroup K) (hYB : Y ≤ B)
    (hindex : ¬ p ∣ Y.relIndex B) (R : Sylow p Y) :
    ∃ P : Sylow p B,
      (P : Subgroup B).map B.subtype = (R : Subgroup Y).map Y.subtype := by
  let : Fact p.Prime := ⟨hp⟩
  let f := Subgroup.inclusion hYB
  let U := (R : Subgroup Y).map f
  have hU : IsPGroup p U := R.isPGroup'.map f
  have hnot : ¬ p ∣ U.index := by
    change ¬ p ∣ ((R : Subgroup Y).map f).index
    rw [(R : Subgroup Y).index_map_of_injective (Subgroup.inclusion_injective hYB),
      Subgroup.inclusion_range]
    exact hp.not_dvd_mul R.not_dvd_index hindex
  let P := hU.toSylow hnot
  refine ⟨P, ?_⟩
  rw [IsPGroup.toSylow_coe, Subgroup.map_map]
  have hcomp : B.subtype.comp f = Y.subtype := by ext a; rfl
  rw [hcomp]

theorem sylow_overgroup_relIndex_prime_to [Finite K]
    (p : ℕ) (hp : p.Prime) (B Y : Subgroup K) (P : Sylow p B)
    (hPY : (P : Subgroup B).map B.subtype ≤ Y) :
    ¬ p ∣ Y.relIndex B := by
  let : Fact p.Prime := ⟨hp⟩
  have hle : (P : Subgroup B) ≤ Y.subgroupOf B := by
    intro a ha
    exact hPY (Subgroup.mem_map_of_mem B.subtype ha)
  exact fun h => P.not_dvd_index
    (h.trans (Subgroup.index_dvd_of_le hle))

theorem subgroup_order_factorization_eq_of_prime_to_relIndex [Finite K]
    (p : ℕ) (B Y : Subgroup K) (hYB : Y ≤ B)
    (hindex : ¬ p ∣ Y.relIndex B) :
    (Nat.card Y).factorization p = (Nat.card B).factorization p := by
  have hcard := (Y.subgroupOf B).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYB).toEquiv] at hcard
  have hidxpos : (Y.subgroupOf B).index ≠ 0 := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos.ne'
  conv_rhs => rw [← hcard]
  rw [Nat.factorization_mul Nat.card_pos.ne' hidxpos]
  change ¬ p ∣ (Y.subgroupOf B).index at hindex
  simp only [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hindex, add_zero]

theorem odd_central_quotient_centralizer_factorization_eq [Finite K]
    (p : ℕ) (J B Y : Subgroup K) [J.Normal] (t : K) (ht : orderOf t = 2)
    (hJodd : Odd (Nat.card J)) (hYB : Y ≤ B) (hJY : J ≤ Y)
    (hcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J))
    (hindex : ¬ p ∣ Y.relIndex B) :
    (Nat.card (Y ⊓ Subgroup.centralizer ({t} : Set K) : Subgroup K)).factorization p =
      (Nat.card (B ⊓ Subgroup.centralizer ({t} : Set K) : Subgroup K)).factorization p := by
  let C := Subgroup.centralizer ({t} : Set K)
  have hi := (odd_central_quotient_subgroup_centralizer_index J Y t ht hJodd hJY hcentral).trans
    (odd_central_quotient_subgroup_centralizer_index J B t ht hJodd
      (hJY.trans hYB) hcentral).symm
  have hi0 : C.relIndex B ≠ 0 := by
    change (C.subgroupOf B).index ≠ 0
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos.ne'
  have hYcard := C.relIndex_mul_card Y
  have hBcard := C.relIndex_mul_card B
  rw [inf_comm C Y, hi] at hYcard
  rw [inf_comm C B] at hBcard
  have hYfac := congrArg (fun n : ℕ => n.factorization p) hYcard
  have hBfac := congrArg (fun n : ℕ => n.factorization p) hBcard
  rw [Nat.factorization_mul hi0 Nat.card_pos.ne', Finsupp.add_apply] at hYfac hBfac
  have horder := subgroup_order_factorization_eq_of_prime_to_relIndex p B Y hYB hindex
  change (Nat.card Y).factorization p = (Nat.card B).factorization p at horder
  exact Nat.add_left_cancel (hYfac.trans (horder.trans hBfac.symm))

end CFSG.ProperTwoGeneratedCore
