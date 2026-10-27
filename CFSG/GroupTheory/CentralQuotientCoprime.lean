module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.GroupTheory

theorem eq_of_mk_eq_of_pow_eq_one_of_coprime {H : Type*} [Group H] {Z : Subgroup H} [Z.Normal]
    (hZc : Z ≤ Subgroup.center H) {r : ℕ} (hZ : Nat.Coprime r (Nat.card Z)) {u v : H}
    (hu : u ^ r = 1) (hv : v ^ r = 1) (huv : (u : H ⧸ Z) = v) : u = v := by
  have hc : u * v⁻¹ ∈ Z := by
    simpa [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp huv
  have hcomm : Commute u v := by
    have h := Subgroup.mem_center_iff.mp (hZc hc) v
    rw [inv_mul_cancel_right, ← mul_assoc, mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hcr : (u * v⁻¹) ^ r = 1 := by
    rw [hcomm.inv_right.mul_pow, hu, inv_pow, hv, inv_one, mul_one]
  have hcZ : (u * v⁻¹) ^ Nat.card Z = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard Z hc)
  have h1 := pow_gcd_eq_one.mpr ⟨hcr, hcZ⟩
  rwa [hZ.gcd_eq_one, pow_one, mul_inv_eq_one] at h1

end CFSG.GroupTheory

end
