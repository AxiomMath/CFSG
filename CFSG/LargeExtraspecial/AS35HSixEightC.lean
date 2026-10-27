module

public import CFSG.LargeExtraspecial.AS35HQuotSet
public import CFSG.LargeExtraspecial.AS35HSixEightA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CQuot

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem orderOf_rhoL_eq_three {x : G} (hxM : x ∈ S.M) (hx3 : orderOf x = 3) :
    orderOf (S.rhoL hxM) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxQ : x ∉ S.QG := by
    intro hxQ
    have h4 := S.pow_four_of_mem_QG hxQ
    have h3 := pow_three_of_orderOf hx3
    have h1 : x = 1 := by
      calc x = x ^ 4 * (x ^ 3)⁻¹ := by group
        _ = 1 := by rw [h4, h3]; group
    rw [h1, orderOf_one] at hx3
    exact absurd hx3 (by norm_num)
  refine orderOf_eq_prime ?_ (S.rhoL_ne_one hxM hxQ)
  change ((S.ρ ⟨x, hxM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ 3 = 1
  rw [← Subgroup.coe_pow, ← map_pow]
  have h1 : (⟨x, hxM⟩ : S.M) ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact pow_three_of_orderOf hx3)
  rw [h1, map_one]
  rfl

theorem fixSpace_rt (hS : S.SixHyp) {r t : G} (hr : r ∈ S.DSet) (ht : t ∈ S.DSet)
    (hrM : r ∈ S.M) (htM : t ∈ S.M) (h3 : orderOf (r * t) = 3) :
    fixSpace (S.rhoL (S.M.mul_mem hrM htM)) = fixSpace (S.rhoL hrM) ⊓ fixSpace (S.rhoL htM) ∧
      finrank (ZMod 2) (fixSpace (S.rhoL (S.M.mul_mem hrM htM))) + 4 = 2 * S.width := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hAr := (S.fiveOne_two hS.sixFour hS.weak hr hrM).1
  have hAt := (S.fiveOne_two hS.sixFour hS.weak ht htM).1
  have h3' : orderOf (S.rhoL hrM * S.rhoL htM) = 3 := by
    rw [← S.rhoL_mul_mem hrM htM]
    exact S.orderOf_rhoL_eq_three _ h3
  obtain ⟨-, -, h4, -, h5⟩ := commSpace_mul_of_orderOf_eq_three S.q_nondegenerate hAr hAt h3'
  rw [S.rhoL_mul_mem hrM htM]
  refine ⟨h5, ?_⟩
  have h6 := finrank_commSpace_add_finrank_fixSpace (S.rhoL hrM * S.rhoL htM)
  rw [S.finrank_Qt_eq_two_mul_width, h4] at h6
  omega

theorem commute_of_mem_cqx_rt (hS : S.SixHyp) {r t : G} (hr : r ∈ S.DSet) (ht : t ∈ S.DSet)
    (hrM : r ∈ S.M) (htM : t ∈ S.M) (h3 : orderOf (r * t) = 3) {d : G} (hdQ : d ∈ S.QG)
    (hdx : d * (r * t) = r * t * d) : t * d * t⁻¹ = d := by
  have h1 : S.cl d ∈ fixSpace (S.rhoL (S.M.mul_mem hrM htM)) := by
    rw [mem_fixSpace, S.rhoL_cl _ hdQ]
    congr 1
    calc r * t * d * (r * t)⁻¹ = d * (r * t) * (r * t)⁻¹ := by rw [hdx]
      _ = d := by group
  rw [(S.fixSpace_rt hS hr ht hrM htM h3).1] at h1
  have h2 := (Submodule.mem_inf.mp h1).2
  rw [mem_fixSpace, S.rhoL_cl htM hdQ] at h2
  exact S.conj_eq_of_cl_conj_eq hS.sixFour hS.weak ht htM hdQ h2

omit [Finite G] in
theorem conj_rt_eq_inv {r t : G} (hrr : r * r = 1) (htt : t * t = 1) :
    t * (r * t) * t⁻¹ = (r * t)⁻¹ := by
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hrr
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  rw [mul_inv_rev, hrinv, htinv]
  calc t * (r * t) * t = t * r * (t * t) := by group
    _ = t * r := by rw [htt, mul_one]

end Setting

end CFSG.LargeExtraspecial
