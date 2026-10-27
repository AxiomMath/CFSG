module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4B
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedInner
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F]

abbrev e4 : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv

theorem val_e4_inl (i : Fin 2) : ((e4 (Sum.inl i) : Fin 4) : ℕ) = i := rfl

theorem val_e4_inr (i : Fin 2) : ((e4 (Sum.inr i) : Fin 4) : ℕ) = 2 + i := rfl

@[expose] noncomputable def bv :
    Matrix (Fin 4) (Fin 4) F ≃ₐ[F] Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.reindexAlgEquiv F F e4.symm

theorem bv_apply (M : Matrix (Fin 4) (Fin 4) F) (i j : Fin 2 ⊕ Fin 2) :
    bv M i j = M (e4 i) (e4 j) := rfl

theorem trace_bv (M : Matrix (Fin 4) (Fin 4) F) : (bv M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, bv_apply]
  exact Equiv.sum_comp e4 (fun i => M i i)

abbrev diag4 : Matrix (Fin 4) (Fin 4) F := diagonal fun i => if (i : ℕ) < 2 then 1 else -1

theorem bv_diag4 : bv (diag4 : Matrix (Fin 4) (Fin 4) F) = dD := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [bv_apply, val_e4_inl, val_e4_inr]

theorem trace_diag4 : (diag4 : Matrix (Fin 4) (Fin 4) F).trace = 0 := by
  simp [Matrix.trace, Fin.sum_univ_four]

theorem exists_conj_diag4 (hK : ringChar F ≠ 2) {B : GL (Fin 4) F} (hB : B * B = 1)
    (hk : finrank F (LinearMap.ker (toLin' B.val - 1)) = 2) :
    ∃ P : GL (Fin 4) F, ((P⁻¹ * B * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = diag4 := by
  have hBm : (B : Matrix (Fin 4) (Fin 4) F) * B = 1 := by
    rw [← Units.val_mul, hB, Units.val_one]
  obtain ⟨b, hb⟩ := exists_eigenbasis hK hBm
  obtain ⟨P, D, hPD, hD⟩ := exists_gl_inv_mul_mul_eq_toMatrix b B
  refine ⟨P, ?_⟩
  rw [hPD, hD]
  ext a c
  rw [LinearMap.toMatrix_apply, toLin'_apply, hb c, map_smul, Basis.repr_self,
    Finsupp.smul_apply, Finsupp.single_apply]
  simp only [diag4, diagonal_apply, hk]
  by_cases hac : a = c
  · subst hac
    simp
  · simp [hac, Ne.symm hac]

theorem trace_eq_zero_of_finrank (hK : ringChar F ≠ 2) {B : GL (Fin 4) F} (hB : B * B = 1)
    (hk : finrank F (LinearMap.ker (toLin' B.val - 1)) = 2) :
    (B : Matrix (Fin 4) (Fin 4) F).trace = 0 := by
  obtain ⟨P, hP⟩ := exists_conj_diag4 hK hB hk
  rw [← trace_diag4, ← hP, Units.val_mul, Units.val_mul, trace_mul_comm, ← Matrix.mul_assoc,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem isSquare_of_eigvec {A : Matrix (Fin 4) (Fin 4) F} {c ν : F}
    (hA : A * A = c • 1) {v : Fin 4 → F} (hv0 : v ≠ 0) (hv : A *ᵥ v = ν • v) : IsSquare c := by
  refine ⟨ν, ?_⟩
  have h : (A * A) *ᵥ v = (ν * ν) • v := by
    rw [← mulVec_mulVec, hv, mulVec_smul, hv, smul_smul]
  rw [hA, smul_mulVec, one_mulVec] at h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hi this

theorem isSquare_of_roweig {A : Matrix (Fin 4) (Fin 4) F} {c ν : F}
    (hA : A * A = c • 1) {v : Fin 4 → F} (hv0 : v ≠ 0) (hv : v ᵥ* A = ν • v) : IsSquare c := by
  refine ⟨ν, ?_⟩
  have h : v ᵥ* (A * A) = (ν * ν) • v := by
    rw [← vecMul_vecMul, hv, smul_vecMul, hv, smul_smul]
  rw [hA, vecMul_smul, vecMul_one] at h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hi this

theorem eq_one_of_common_eigvec {A₁ A₂ : GL (Fin 4) F} {lam : F}
    (h : (A₁ : Matrix (Fin 4) (Fin 4) F) * A₂ = lam • ((A₂ : Matrix (Fin 4) (Fin 4) F) * A₁))
    {v : Fin 4 → F} (hv0 : v ≠ 0) {ν₁ ν₂ : F} (h₁ : (A₁ : Matrix (Fin 4) (Fin 4) F) *ᵥ v = ν₁ • v)
    (h₂ : (A₂ : Matrix (Fin 4) (Fin 4) F) *ᵥ v = ν₂ • v) : lam = 1 := by
  have hν : ∀ (A : GL (Fin 4) F) (ν : F), (A : Matrix (Fin 4) (Fin 4) F) *ᵥ v = ν • v → ν ≠ 0 := by
    intro A ν hA hν0
    rw [hν0, zero_smul] at hA
    apply hv0
    have := congrArg (fun w => ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ w) hA
    simpa [mulVec_mulVec, ← Units.val_mul] using this
  have e := congrArg (fun M => M *ᵥ v) h
  simp only [smul_mulVec, ← mulVec_mulVec, h₁, h₂, mulVec_smul, smul_smul] at e
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have := congrFun e i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  have hne : ν₁ * ν₂ ≠ 0 := mul_ne_zero (hν A₁ ν₁ h₁) (hν A₂ ν₂ h₂)
  have h3 : (1 - lam) * (ν₁ * ν₂ * v i) = 0 := by linear_combination this
  have h4 := (mul_eq_zero.mp h3).resolve_right (mul_ne_zero hne hi)
  linear_combination -h4

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
