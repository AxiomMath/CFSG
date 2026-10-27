module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ADefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly
open scoped MatrixGroups

private theorem mul_comm_of_mem_kernel {G : Type} [Group G] {Z : Subgroup G}
    (hZc : Z ≤ Subgroup.center G) {p d : ℕ} (hcop : Nat.Coprime p d)
    (hZd : ∀ z ∈ Z, z ^ d = 1) {a g : G} (ha : a ^ p = 1)
    (hmem : g * a * g⁻¹ * a⁻¹ ∈ Z) : g * a = a * g := by
  have hc : Commute (g * a * g⁻¹ * a⁻¹) a :=
    (Subgroup.mem_center_iff.mp (hZc hmem) a).symm
  have hzp : (g * a * g⁻¹ * a⁻¹) ^ p = 1 := by
    have h1 : (g * a * g⁻¹) ^ p = 1 := by rw [conj_pow, ha]; simp
    have h2 : g * a * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * a := by group
    rw [h2, Commute.mul_pow hc, ha, mul_one] at h1
    exact h1
  have hz1 : g * a * g⁻¹ * a⁻¹ = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_iff_pow_eq_one.mpr hzp)
      (orderOf_dvd_iff_pow_eq_one.mpr (hZd _ hmem)))
  have hconj : g * a * g⁻¹ = a := by
    rw [show g * a * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * a by group, hz1, one_mul]
  calc g * a = g * a * g⁻¹ * g := by group
    _ = a * g := by rw [hconj]

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
