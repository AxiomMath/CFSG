module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1U4Mat

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K]

theorem shape_u4_one (h : UnitaryFieldData p f K) (h2 : (2 : K) ≠ 0)
    (A A' : Matrix (HypIndex 2 0) (HypIndex 2 0) K) (hA'A : A' * A = 1) (σ : K ≃+* K)
    {c0 : K} (hc0 : c0 ≠ 0) (hc0b : h.bar c0 = -c0)
    (hR1 : A * (single ue1 uf1 c0).map σ = single ue1 uf1 c0 * A)
    (hR2 : ∀ t, A * (single ue2 uf1 t - single ue1 uf2 (h.bar t)).map σ =
      (single ue2 uf1 t - single ue1 uf2 (h.bar t)) * A)
    (hR3 : ∀ t, A * (single ue1 ue2 t - single uf2 uf1 (h.bar t)).map σ =
      (single ue1 ue2 t - single uf2 uf1 (h.bar t)) * A) :
    (∀ c, σ c = c) ∧ ∃ a : K, a ≠ 0 ∧ (A - a • 1) * (A - a • 1) = 0 := by
  have z21 : A ue2 ue1 = 0 := by simpa [hc0] using entry_comm₁ A σ ue1 uf1 c0 hR1 ue2 uf1
  have z31 : A uf1 ue1 = 0 := by simpa [hc0] using entry_comm₁ A σ ue1 uf1 c0 hR1 uf1 uf1
  have z41 : A uf2 ue1 = 0 := by simpa [hc0] using entry_comm₁ A σ ue1 uf1 c0 hR1 uf2 uf1
  have z32 : A uf1 ue2 = 0 := by simpa [hc0] using entry_comm₁ A σ ue1 uf1 c0 hR1 ue1 ue2
  have z34 : A uf1 uf2 = 0 := by simpa [hc0] using entry_comm₁ A σ ue1 uf1 c0 hR1 ue1 uf2
  have h11 : A' ue1 ue1 * A ue1 ue1 = 1 := by
    have := congrFun (congrFun hA'A ue1) ue1
    rw [Matrix.mul_apply, sum_hyp4, Matrix.one_apply_eq] at this
    simpa [z21, z31, z41] using this
  have ha0 : A ue1 ue1 ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at h11
    exact zero_ne_one h11
  have hA22 : A ue2 ue2 = A ue1 ue1 := by
    have e := entry_comm₂ A σ ue1 ue2 uf2 uf1 1 (h.bar 1) (hR3 1) ue1 ue2
    simp at e
    linear_combination -e
  have hσ : ∀ t, σ t = t := fun t => by
    have e := entry_comm₂ A σ ue1 ue2 uf2 uf1 t (h.bar t) (hR3 t) ue1 ue2
    simp at e
    rw [hA22] at e
    exact mul_left_cancel₀ ha0 (by rw [e, mul_comm])
  have hd3 : A uf2 uf2 = A uf1 uf1 := by
    have e := entry_comm₂ A σ ue1 ue2 uf2 uf1 1 (h.bar 1) (hR3 1) uf2 uf1
    simp [hσ] at e
    linear_combination e
  have hA44 : A uf2 uf2 = A ue1 ue1 := by
    have e := entry_comm₂ A σ ue2 uf1 ue1 uf2 1 (h.bar 1) (hR2 1) ue1 uf2
    simp [hσ] at e
    linear_combination -e
  have hA33 : A uf1 uf1 = A ue1 ue1 := hd3.symm.trans hA44
  have z42 : A uf2 ue2 = 0 := by
    have e := entry_comm₂ A σ ue2 uf1 ue1 uf2 1 (h.bar 1) (hR2 1) uf2 uf1
    simpa using e
  have z23' : A ue2 uf2 = 0 := by
    have e := entry_comm₂ A σ ue1 ue2 uf2 uf1 1 (h.bar 1) (hR3 1) ue1 uf2
    simpa using e.symm
  have z14 : A ue1 uf2 = 0 := by
    have e1 := entry_comm₂ A σ ue1 ue2 uf2 uf1 1 (h.bar 1) (hR3 1) ue1 uf1
    have e2 := entry_comm₂ A σ ue1 ue2 uf2 uf1 c0 (h.bar c0) (hR3 c0) ue1 uf1
    simp [hσ, hc0b] at e1 e2
    have : (2 * c0) * A ue1 uf2 = 0 := by linear_combination e2 - c0 * e1
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hc0)
  have z23 : A ue2 uf1 = 0 := by
    have e1 := entry_comm₂ A σ ue1 ue2 uf2 uf1 1 (h.bar 1) (hR3 1) ue1 uf1
    simp [hσ, z14] at e1
    exact e1.symm
  refine ⟨hσ, A ue1 ue1, ha0, ?_⟩
  have key : ∀ i j, ((A - A ue1 ue1 • 1) * (A - A ue1 ue1 • 1)) i j = 0 := by
    refine hyp4_cases ?_ ?_ ?_ ?_ <;> refine hyp4_cases ?_ ?_ ?_ ?_ <;>
      simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, z21, z31, z41, z32,
        z34, z42, z23', z14, z23, hA22, hA33, hA44]
  ext i j
  exact key i j

theorem shape_u4_two (h : UnitaryFieldData p f K)
    (A A' : Matrix (HypIndex 2 0) (HypIndex 2 0) K) (hA'A : A' * A = 1) (σ : K ≃+* K)
    {c0 : K} (hc0 : c0 ≠ 0)
    (hR1 : A * (single ue1 uf1 c0).map σ = single ue1 uf1 c0 * A)
    (hR4 : A * (single ue2 uf2 c0).map σ = single ue2 uf2 c0 * A)
    (hR2 : ∀ t, A * (single ue2 uf1 t - single ue1 uf2 (h.bar t)).map σ =
      (single ue2 uf1 t - single ue1 uf2 (h.bar t)) * A) :
    (∀ c, σ c = c) ∧ ∃ a : K, a ≠ 0 ∧ (A - a • 1) * (A - a • 1) = 0 := by
  have z21 : A ue2 ue1 = 0 := by simpa [hc0] using entry_comm₁ A σ ue1 uf1 c0 hR1 ue2 uf1
  have z31 : A uf1 ue1 = 0 := by simpa [hc0] using entry_comm₁ A σ ue1 uf1 c0 hR1 uf1 uf1
  have z41 : A uf2 ue1 = 0 := by simpa [hc0] using entry_comm₁ A σ ue1 uf1 c0 hR1 uf2 uf1
  have z32 : A uf1 ue2 = 0 := by simpa [hc0] using entry_comm₁ A σ ue1 uf1 c0 hR1 ue1 ue2
  have z34 : A uf1 uf2 = 0 := by simpa [hc0] using entry_comm₁ A σ ue1 uf1 c0 hR1 ue1 uf2
  have z12 : A ue1 ue2 = 0 := by simpa [hc0] using entry_comm₁ A σ ue2 uf2 c0 hR4 ue1 uf2
  have z42 : A uf2 ue2 = 0 := by simpa [hc0] using entry_comm₁ A σ ue2 uf2 c0 hR4 uf2 uf2
  have z43 : A uf2 uf1 = 0 := by simpa [hc0] using entry_comm₁ A σ ue2 uf2 c0 hR4 ue2 uf1
  have h11 : A' ue1 ue1 * A ue1 ue1 = 1 := by
    have := congrFun (congrFun hA'A ue1) ue1
    rw [Matrix.mul_apply, sum_hyp4, Matrix.one_apply_eq] at this
    simpa [z21, z31, z41] using this
  have ha0 : A ue1 ue1 ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at h11
    exact zero_ne_one h11
  have hA44 : A uf2 uf2 = A ue1 ue1 := by
    have e := entry_comm₂ A σ ue2 uf1 ue1 uf2 1 (h.bar 1) (hR2 1) ue1 uf2
    simp at e
    linear_combination -e
  have hσb : ∀ t, σ (h.bar t) = h.bar t := fun t => by
    have e := entry_comm₂ A σ ue2 uf1 ue1 uf2 t (h.bar t) (hR2 t) ue1 uf2
    simp at e
    rw [hA44] at e
    exact mul_left_cancel₀ ha0 (by rw [e, mul_comm])
  have hσ : ∀ t, σ t = t := fun t => by
    have := hσb (h.bar t)
    rwa [h.bar_bar] at this
  have hA33 : A uf1 uf1 = A ue1 ue1 := by
    have e := entry_comm₁ A σ ue1 uf1 c0 hR1 ue1 uf1
    simp [hσ] at e
    exact mul_left_cancel₀ hc0 (by linear_combination -e)
  have hA22 : A ue2 ue2 = A ue1 ue1 := by
    have e := entry_comm₂ A σ ue2 uf1 ue1 uf2 1 (h.bar 1) (hR2 1) ue2 uf1
    simp [hσ] at e
    linear_combination e + hA33
  refine ⟨hσ, A ue1 ue1, ha0, ?_⟩
  have key : ∀ i j, ((A - A ue1 ue1 • 1) * (A - A ue1 ue1 • 1)) i j = 0 := by
    refine hyp4_cases ?_ ?_ ?_ ?_ <;> refine hyp4_cases ?_ ?_ ?_ ?_ <;>
      simp [Matrix.mul_apply, Matrix.sub_apply, Matrix.one_apply, z21, z31, z41, z32,
        z34, z12, z42, z43, hA22, hA33, hA44]
  ext i j
  exact key i j

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
