module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4PrimeKernels
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.ZInvariantTen
public import CFSG.Sporadic.Schreier.J4SElevenBase1

public noncomputable section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem comm_zpow_of_comm {G : Type*} [Group G] {a b : G} (h : a * b = b * a) (k : ℤ) :
    a ^ k * b = b * a ^ k :=
  (Commute.zpow_left (show Commute a b from h) k).eq

theorem zpow_pow_eq_one_of_orderOf {G : Type*} [Group G] {c : G} {r : ℕ} (hc : orderOf c = r)
    (k : ℤ) : (c ^ k) ^ r = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hc, pow_orderOf_eq_one,
    one_zpow]

theorem comm_inv_of_comm {G : Type*} [Group G] {a b : G} (h : a * b = b * a) :
    a * b⁻¹ = b⁻¹ * a :=
  (Commute.inv_right (show Commute a b from h)).eq

theorem not_commute_qz_of_prime
    {r : ℕ} (hr : r ∈ ({5, 7, 23, 29, 31, 37, 43} : Finset ℕ)) {c : J} (hc : orderOf c = r) :
    c * qz ≠ qz * c := by
  intro hcz
  have hrp : r.Prime := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hr5 : 5 ≤ r := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    omega
  obtain ⟨c', hc', f, hf, hnd⟩ := exists_prime_kernel_poly hr hc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
  have hc'z : c ^ k * qz⁻¹ = qz⁻¹ * c ^ k := @comm_inv_of_comm J (Subgroup.toGroup J) _ _ (@comm_zpow_of_comm J (Subgroup.toGroup J) _ _ hcz k)
  have hc'r : (c ^ k) ^ r = 1 := @zpow_pow_eq_one_of_orderOf J (Subgroup.toGroup J) _ _ hc k
  have hq11 : qz ^ 11 = 1 := by
    have := pow_orderOf_eq_one qz
    rwa [orderOf_qz] at this
  have hz11 : (rowLin qz⁻¹) ^ 11 = 1 := by
    rw [← map_pow, inv_pow, hq11, inv_one, map_one]
  refine not_commute_of_not_ten_dvd_finrank_ker_aeval (rowLin qz⁻¹) hz11 ?_ (rowLin (c ^ k))
    hrp hr5 ?_ f hf hnd ?_
  · have h1 : ((rowLin qz⁻¹ : (Fin 112 → ZMod 2) ≃ₗ[ZMod 2] (Fin 112 → ZMod 2)) :
        (Fin 112 → ZMod 2) →ₗ[ZMod 2] (Fin 112 → ZMod 2)) - 1 =
        Matrix.vecMulLinear (φ qz) - 1 := by rw [rowLin_inv_eq]
    rw [h1]
    have h2 : LinearMap.ker (Matrix.vecMulLinear (φ qz) - 1) = rowFix (φ qz) := by
      ext w
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
        Matrix.vecMulLinear_apply, mem_rowFix]
    rw [h2]
    exact finrank_rowFix_qz
  · rw [← map_pow, hc'r, map_one]
  · rw [← map_mul, ← map_mul, hc'z]

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
