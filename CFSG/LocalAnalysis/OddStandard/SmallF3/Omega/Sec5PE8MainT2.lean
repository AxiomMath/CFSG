module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPCls

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.GH74.GLS.Th2.P412

theorem sec5pe8m_cls_t_order {G : Type} [Group G] [Finite G] {X : Type} [Group X] [Finite X]
    {t z : G} {T : Subgroup G} {π : ↥(centralizer ({z} : Set G)) →* X}
    (hyp : Sec5OPHyp t z T π) :
    orderOf (sec5op_cls hyp ⟨t, sec5op_t_mem_Y t z⟩) = 2 := by
  let y : ↥(sec5op_Y t z) := ⟨t, sec5op_t_mem_Y t z⟩
  let u : ↥(centralizer ({z} : Set G)) := ⟨t, hyp.tH⟩
  let M : Subgroup X := normalClosure ((sec5op_Tb z T π : Subgroup X) : Set X)
  let m : ↥M := ⟨π u, sec5op_pi_mem hyp y.2⟩
  have hcls : sec5op_cls hyp y = sec5g_pi (sec5op_Tb z T π) m := by
    change sec5g_pi (sec5op_Tb z T π)
        ⟨π ⟨y.1, sec5op_Y_le hyp.tH y.2⟩, sec5op_pi_mem hyp y.2⟩ =
      sec5g_pi (sec5op_Tb z T π) m
    congr 1
  have hu2 : orderOf u = 2 := (Subgroup.orderOf_mk t hyp.tH).trans hyp.ht
  have hu_sq : u * u = 1 := by
    have h : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
    simpa [pow_two] using h
  have hm_sq : m * m = 1 := by
    apply Subtype.ext
    change π u * π u = 1
    rw [← map_mul, hu_sq, map_one]
  have hc_sq : sec5op_cls hyp y * sec5op_cls hyp y = 1 := by
    rw [hcls, ← map_mul, hm_sq, map_one]
  have hc_ne : sec5op_cls hyp y ≠ 1 := by
    intro hc1
    have hm1 : sec5g_pi (sec5op_Tb z T π) m = 1 := hcls ▸ hc1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm1
    have hm_eq_one : m = 1 := eq_one_of_mem_oddCore_of_sq hm1 hm_sq
    have hpu : π u = 1 := by
      have := congrArg Subtype.val hm_eq_one
      simpa [m] using this
    have hker : u ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      exact hpu
    rw [hyp.ker] at hker
    exact hyp.t_not_mem (Subgroup.mem_subgroupOf.mp hker)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hc_sq) hc_ne

end CFSG.OddStandard.SmallF3.Omega
