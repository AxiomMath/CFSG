module

public import CFSG.GH74.KGroups.M11
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup CFSG.Blueprint

theorem solvable_centralizer_of_M11
    {K : Type} [Group K] (h : NativeSporadic.IsSporadic K .M11)
    (hz : center K = ⊥) (z : K) (hz2 : orderOf z = 2) :
    Group.IsSolvable ↥(centralizer ({z} : Set K)) := by
  have hsq : z * z = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hz2)
  have hα2 : (MulAut.conj z) ^ 2 = 1 := by
    rw [← map_pow, pow_two, hsq, map_one]
  have hα1 : (MulAut.conj z) ≠ 1 := by
    intro h1
    have hzc : z ∈ center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut K => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * z = z * g * z⁻¹ * z := by rw [this]
        _ = z * g := by group
    rw [hz, Subgroup.mem_bot] at hzc
    rw [hzc, orderOf_one] at hz2
    omega
  exact KGroups.M11.fixed_solvable h (MulAut.conj z) hα2 hα1 (centralizer ({z} : Set K))
    (fun x hx => by
      have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
      simp only [MulAut.conj_apply]
      calc z * x * z⁻¹ = x * z * z⁻¹ := by rw [← hx']
        _ = x := by group)

end CFSG.GH74.GLS.TwoThin
