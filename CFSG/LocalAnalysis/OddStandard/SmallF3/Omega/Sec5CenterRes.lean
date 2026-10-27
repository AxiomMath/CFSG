module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec5_twoPrimeRes_le {G : Type} [Group G] (H : Subgroup G) :
    twoPrimeRes H ≤ H := by
  rw [twoPrimeRes]
  exact (Subgroup.closure_le H).mpr fun _ hx => hx.1

private theorem sec5_twoPrimeRes_subgroupOf_normal {G : Type} [Group G] (X : Subgroup G) :
    ((twoPrimeRes X).subgroupOf X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  change (g : G) * (n : G) * (g : G)⁻¹ ∈ twoPrimeRes X
  refine Subgroup.closure_induction (fun a ha => ?_) ?_ (fun a b _ _ iha ihb => ?_)
    (fun a _ iha => ?_) hn
  · rw [twoPrimeRes]
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · exact X.mul_mem (X.mul_mem g.2 ha.1) (X.inv_mem g.2)
    · obtain ⟨k, hk⟩ := ha.2
      have hconj : SemiconjBy (g : G) a ((g : G) * a * (g : G)⁻¹) := by
        show (g : G) * a = (g : G) * a * (g : G)⁻¹ * (g : G)
        group
      exact ⟨k, by rw [← hk]; exact (SemiconjBy.orderOf_eq (g : G) hconj).symm⟩
  · simp
  · convert mul_mem iha ihb using 1
    group
  · convert inv_mem iha using 1
    group

theorem sec5_twoPrimeRes_eq_self [Finite G] {X : Subgroup G} (hX : IsQuasisimple X)
    (h2 : 2 ∣ Nat.card (X ⧸ center X)) : twoPrimeRes X = X := by
  have hOpen : CFSG.Open.IsQuasisimple ↥X := ⟨Group.isPerfect_def.mp hX.1, hX.2.1⟩
  refine le_antisymm (sec5_twoPrimeRes_le X) ?_
  haveI : ((twoPrimeRes X).subgroupOf X).Normal := sec5_twoPrimeRes_subgroupOf_normal X
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hOpen
    ((twoPrimeRes X).subgroupOf X) with hle | htop
  · exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨xbar, hxbar⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥X ⧸ Subgroup.center ↥X) 2 h2
    let q : ↥X →* (↥X ⧸ Subgroup.center ↥X) := QuotientGroup.mk' (Subgroup.center ↥X)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥X) xbar
    change orderOf (q x) = 2 at hxbar
    have hqx_ne : q x ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hxbar
      norm_num at hxbar
    have hqx_sq : (q x) ^ 2 = 1 := by rw [← hxbar, pow_orderOf_eq_one]
    have hxord_ne : orderOf x ≠ 0 := by
      have hfin : IsOfFinOrder x :=
        isOfFinOrder_iff_pow_eq_one.mpr ⟨Nat.card ↥X, Nat.card_pos, pow_card_eq_one'⟩
      exact hfin.orderOf_pos.ne'
    obtain ⟨a, b, hbodd, hxord⟩ := Nat.exists_eq_two_pow_mul_odd hxord_ne
    let y : ↥X := x ^ b
    have hqy : q y = q x := by
      show q (x ^ b) = q x
      rw [map_pow]
      obtain ⟨t, ht⟩ := hbodd
      rw [ht, pow_add, pow_mul, hqx_sq, one_pow, one_mul, pow_one]
    have hy_pow : y ^ (2 ^ a) = 1 := by
      show (x ^ b) ^ (2 ^ a) = 1
      rw [← pow_mul, mul_comm b (2 ^ a), ← hxord, pow_orderOf_eq_one]
    have hydvd : orderOf y ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one hy_pow
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hydvd
    have hyY : (y : G) ∈ twoPrimeRes X :=
      Subgroup.subset_closure ⟨y.2, ⟨j, by rw [Subgroup.orderOf_coe, hj]⟩⟩
    have hy' : y ∈ (twoPrimeRes X).subgroupOf X := Subgroup.mem_subgroupOf.mpr hyY
    have hqy1 : q y = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hle hy'
    rw [hqy] at hqy1
    exact hqx_ne hqy1
  · intro x hx
    have : (⟨x, hx⟩ : ↥X) ∈ (twoPrimeRes X).subgroupOf X := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

end CFSG.OddStandard.SmallF3.Omega
