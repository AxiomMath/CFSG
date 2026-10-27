module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.ClassicalInvolution.Asc77.T3Core

variable {Y : Type} [Group Y]

theorem exists_conj_of_mul_mem_odd {u x : Y} (hu : u * u = 1) (hx : x * x = 1)
    (hodd : Odd (orderOf (u * x))) : ∃ k : ℕ, (u * x) ^ k * u * ((u * x) ^ k)⁻¹ = x := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨k, ?_⟩
  set t : Y := u * x with ht
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hord : t ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one t
  have hconj : u * t * u⁻¹ = t⁻¹ := by
    rw [ht, mul_inv_rev, hui, hxi]
    calc u * (u * x) * u = (u * u) * x * u := by group
      _ = x * u := by rw [hu, one_mul]
  have hconjk : u * t ^ k * u⁻¹ = (t ^ k)⁻¹ := by
    have := map_pow (MulAut.conj u) t k
    simp only [MulAut.conj_apply] at this
    rw [this, hconj, inv_pow]
  have h2k : t ^ (2 * k) = t⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hord
  calc t ^ k * u * (t ^ k)⁻¹ = t ^ k * (u * (t ^ k)⁻¹ * u⁻¹) * u := by group
    _ = t ^ k * t ^ k * u := by
        congr 2
        have := congrArg (fun w => w⁻¹) hconjk
        simpa [mul_inv_rev, mul_assoc] using this
    _ = t ^ (2 * k) * u := by rw [← pow_add, show k + k = 2 * k by omega]
    _ = x := by
        rw [h2k, ht, mul_inv_rev, hxi, hui]
        calc x * u * u = x * (u * u) := by group
          _ = x := by rw [hu, mul_one]

theorem exists_conj_of_map_eq_of_involutions [Finite Y] {N : Subgroup Y} [N.Normal]
    (hN : Odd (Nat.card N)) {u x : Y} (hu : u * u = 1) (hx : x * x = 1)
    (h : QuotientGroup.mk' N u = QuotientGroup.mk' N x) : ∃ n ∈ N, n * u * n⁻¹ = x := by
  have hux : u * x ∈ N := by
    have h1 : QuotientGroup.mk' N (u * x) = 1 := by
      rw [map_mul, h, ← map_mul, hx, map_one]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hodd : Odd (orderOf (u * x)) :=
    hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hux)
  obtain ⟨k, hk⟩ := exists_conj_of_mul_mem_odd hu hx hodd
  exact ⟨(u * x) ^ k, N.pow_mem hux k, hk⟩

end CFSG.ClassicalInvolution.Asc77.T3Core
