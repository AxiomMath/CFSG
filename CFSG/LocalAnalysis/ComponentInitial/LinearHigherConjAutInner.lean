module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.LocalAnalysis.ComponentInitial.LinearFlag

open Matrix

variable {K : Type*} [Field K] {n : ℕ}

theorem conjAut_mem_range_conj_of_det_eq_pow {A : GL (Fin n) K} {μ : Kˣ}
    (h : GeneralLinearGroup.det A = μ ^ n) :
    conjAut n K A ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  have hdet : GeneralLinearGroup.det ((GeneralLinearGroup.scalar (Fin n) μ)⁻¹ * A) = 1 := by
    rw [map_mul, map_inv, GeneralLinearGroup.det_scalar, Fintype.card_fin, h, inv_mul_cancel]
  obtain ⟨g, hg⟩ : (GeneralLinearGroup.scalar (Fin n) μ)⁻¹ * A ∈
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact hdet
  refine ⟨proj n K g, ?_⟩
  rw [← conjAut_toGL, hg, map_mul, map_inv, conjAut_scalar, inv_one, one_mul]

theorem pow_mem_range_conj_of_mem_linearAutGroup {β : MulAut (projectiveSL n K)}
    (hβ : β ∈ linearAutGroup n K) :
    β ^ n ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hβ
  rw [← map_pow]
  exact conjAut_mem_range_conj_of_det_eq_pow (μ := GeneralLinearGroup.det A) (map_pow _ _ _)

theorem mem_range_conj_of_mem_linearAutGroup_of_coprime {β : MulAut (projectiveSL n K)}
    (hβ : β ∈ linearAutGroup n K) {m : ℕ} (hm : Nat.Coprime m n) (hβm : β ^ m = 1) :
    β ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  set S := (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range
  have hn : β ^ n ∈ S := pow_mem_range_conj_of_mem_linearAutGroup hβ
  have hab : ((m : ℤ) * Nat.gcdA m n + n * Nat.gcdB m n) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hm, Nat.cast_one]
  have hβ' : β = (β ^ m) ^ Nat.gcdA m n * (β ^ n) ^ Nat.gcdB m n := by
    rw [← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul,
      ← _root_.zpow_add, hab, zpow_one]
  rw [hβ', hβm, _root_.one_zpow, one_mul]
  exact S.zpow_mem hn _

end CFSG.LocalAnalysis.ComponentInitial.LinearFlag
