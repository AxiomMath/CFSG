module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Diag

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def diagGL : (ι → Kˣ) →* GL ι K :=
  (Units.map (Matrix.diagonalRingHom ι K : (ι → K) →+* Matrix ι ι K).toMonoidHom).comp
    MulEquiv.piUnits.symm.toMonoidHom

theorem coe_diagGL (d : ι → Kˣ) :
    ((diagGL d : GL ι K) : Matrix ι ι K) = Matrix.diagonal fun a => (d a : K) :=
  rfl

theorem coe_diagGL_conj (d : ι → Kˣ) (τ : K ≃+* K) (g : GL ι K) (a b : ι) :
    ((diagGL d * glAut τ g * (diagGL d)⁻¹ : GL ι K) : Matrix ι ι K) a b =
      (d a : K) * τ ((g : Matrix ι ι K) a b) * ((d b)⁻¹ : Kˣ) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, coe_diagGL, coe_diagGL, coe_glAut,
    mul_diagonal, diagonal_mul]
  simp [Matrix.map_apply]

end Diag

section Unitary

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ} {h : UnitaryFieldData p f K}

theorem det_hypGram_ne_zero : (hypGram r ε K).det ≠ 0 := by
  have := congrArg Matrix.det (hypGram_mul_self (r := r) (ε := ε) (K := K))
  rw [det_mul, det_one] at this
  exact left_ne_zero_of_mul_eq_one this

theorem norm_det_eq_one_of_mem_hypUnitary {A : GL (HypIndex r ε) K} (hA : A ∈ hypUnitary h r ε) :
    h.norm (A : Matrix (HypIndex r ε) (HypIndex r ε) K).det = 1 := by
  have h1 := congrArg Matrix.det (mem_hypUnitary.mp hA)
  have hdet : ((A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar).det =
      h.bar (A : Matrix (HypIndex r ε) (HypIndex r ε) K).det := (RingHom.map_det h.bar _).symm
  rw [det_mul, det_mul, det_transpose, hdet] at h1
  have h2 : h.bar (A : Matrix (HypIndex r ε) (HypIndex r ε) K).det *
      (A : Matrix (HypIndex r ε) (HypIndex r ε) K).det = 1 :=
    mul_right_cancel₀ (det_hypGram_ne_zero (r := r) (ε := ε) (K := K))
      (by linear_combination h1)
  rw [UnitaryFieldData.norm, mul_comm]
  exact h2

@[expose] noncomputable def torusUnits (h : UnitaryFieldData p f K) (a : Fin r → Kˣ) :
    HypIndex r ε → Kˣ
  | .inl i => a i
  | .inr (.inl _) => 1
  | .inr (.inr i) => (Units.map (h.bar : K →* K) (a i))⁻¹

theorem coe_torusUnits (a : Fin r → Kˣ) (x : HypIndex r ε) :
    (torusUnits (ε := ε) h a x : K) = torusEntries h a (1 : Fin ε → Kˣ) x := by
  rcases x with i | k | i <;> simp [torusUnits, torusEntries]

theorem exists_diagGL_mem_hypUnitary (hr : 1 ≤ r) {A : GL (HypIndex r ε) K}
    (hA : A ∈ hypUnitary h r ε) :
    ∃ d : HypIndex r ε → Kˣ, diagGL d ∈ hypUnitary h r ε ∧
      ((diagGL d : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K).det =
        (A : Matrix (HypIndex r ε) (HypIndex r ε) K).det := by
  have hne : (A : Matrix (HypIndex r ε) (HypIndex r ε) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero
  have hu : Units.mk0 _ hne ∈ (Units.map h.normHom).ker := by
    rw [UnitaryFieldData.mem_ker_normUnits]
    exact norm_det_eq_one_of_mem_hypUnitary hA
  rw [← range_ratioHom hr] at hu
  obtain ⟨a, ha⟩ := hu
  have hdiag : (fun x => (torusUnits (ε := ε) h a x : K)) =
      torusEntries h a (1 : Fin ε → Kˣ) := funext (coe_torusUnits a)
  refine ⟨torusUnits h a, ?_, ?_⟩
  · rw [mem_hypUnitary, coe_diagGL, hdiag]
    exact diagonal_torusEntries_isometry h a (fun k => by simp [UnitaryFieldData.norm])
  · rw [coe_diagGL, hdiag, det_diagonal_torusEntries, torusRatio]
    have := congrArg Units.val ha
    rw [coe_ratioHom] at this
    simpa using this

end Unitary

end CFSG.AGLEmbedding.ParabAutIrr
