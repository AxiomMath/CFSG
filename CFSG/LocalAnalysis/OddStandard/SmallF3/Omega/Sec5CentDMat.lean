module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Mat2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec5cd_commutant (N : Mat2)
    (h : ∀ A : SL2F3, A ^ 4 = 1 → (A : Mat2) * N = N * (A : Mat2)) :
    ∃ c : ZMod 3, N = c • (1 : Mat2) := by
  revert N
  decide +kernel

theorem sec5cd_q8_basis : ∃ a b d : SL2F3, a ^ 4 = 1 ∧ b ^ 4 = 1 ∧ d ^ 4 = 1 ∧
    ∀ X : Mat2, ∃ α β γ δ : ZMod 3,
      X = α • (1 : Mat2) + β • (a : Mat2) + γ • (b : Mat2) + δ • (d : Mat2) := by
  refine ⟨⟨!![0, 1; -1, 0], by rw [Matrix.det_fin_two_of]; decide⟩,
    ⟨!![1, 1; 1, -1], by rw [Matrix.det_fin_two_of]; decide⟩,
    ⟨!![1, -1; -1, -1], by rw [Matrix.det_fin_two_of]; decide⟩, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem sec5cd_mat_scalar (m : Mat2 →ₗ[ZMod 3] Mat2)
    (hL : ∀ A : SL2F3, A ^ 4 = 1 → ∀ X : Mat2, m ((A : Mat2) * X) = (A : Mat2) * m X)
    (hR : ∀ A : SL2F3, A ^ 4 = 1 → ∀ X : Mat2, m (X * (A : Mat2)) = m X * (A : Mat2)) :
    ∃ c : ZMod 3, ∀ X : Mat2, m X = c • X := by
  have hN : ∀ A : SL2F3, A ^ 4 = 1 → (A : Mat2) * m 1 = m 1 * (A : Mat2) := by
    intro A hA
    have h1 := hL A hA 1
    have h2 := hR A hA 1
    rw [Matrix.mul_one] at h1
    rw [Matrix.one_mul] at h2
    exact h1.symm.trans h2
  obtain ⟨c, hc⟩ := sec5cd_commutant (m 1) hN
  obtain ⟨a, b, d, ha, hb, hd, hspan⟩ := sec5cd_q8_basis
  have hmA : ∀ A : SL2F3, A ^ 4 = 1 → m (A : Mat2) = c • (A : Mat2) := by
    intro A hA
    have h1 := hL A hA 1
    rw [Matrix.mul_one] at h1
    rw [h1, hc, Matrix.mul_smul, Matrix.mul_one]
  refine ⟨c, fun X => ?_⟩
  obtain ⟨α, β, γ, δ, rfl⟩ := hspan X
  simp only [map_add, map_smul, hc, hmA a ha, hmA b hb, hmA d hd]
  module

end CFSG.OddStandard.SmallF3.Omega
