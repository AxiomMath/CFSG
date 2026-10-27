module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.GroupTheory

theorem exists_ne_one_apply_eq_inv_of_mul_self_eq_one
    {G : Type*} [Group G] {σ : MulAut G} (hσ : σ * σ = 1)
    (hσ1 : σ ≠ 1) : ∃ x : G, x ≠ 1 ∧ σ x = x⁻¹ := by
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra h
    apply hσ1
    apply MulEquiv.ext
    intro x
    exact not_not.mp (not_exists.mp h x)
  have hσσ : σ (σ x) = x := by
    rw [← MulAut.mul_apply, hσ, MulAut.one_apply]
  refine ⟨σ x * x⁻¹, fun h => hx (mul_inv_eq_one.mp h), ?_⟩
  rw [map_mul, map_inv, hσσ, mul_inv_rev, inv_inv]

theorem mem_of_normal_of_odd_pow_eq_one_of_conj_eq_inv
    {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {g x : G}
    (hg : g ∈ N) {n : ℕ} (hn : Odd n) (hx : x ^ n = 1)
    (hinv : g * x * g⁻¹ = x⁻¹) : x ∈ N := by
  let π := QuotientGroup.mk' N
  have hg1 : π g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
  have hxinv : π x = (π x)⁻¹ := by
    have h := congrArg π hinv
    simpa only [map_mul, map_inv, hg1, one_mul, inv_one, mul_one] using h
  have hx2 : (π x) ^ 2 = 1 := by
    calc (π x) ^ 2 = π x * π x := pow_two _
      _ = π x * (π x)⁻¹ := by nth_rw 2 [hxinv]
      _ = 1 := mul_inv_cancel _
  have hxn : (π x) ^ n = 1 := by rw [← map_pow, hx, map_one]
  obtain ⟨m, rfl⟩ := hn
  rw [pow_succ, pow_mul, hx2, one_pow, one_mul] at hxn
  exact (QuotientGroup.eq_one_iff x).mp hxn

end CFSG.GroupTheory
