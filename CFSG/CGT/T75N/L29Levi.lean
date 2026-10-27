module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData

public section

namespace CFSG.CGT.T75N

open Matrix MatrixGroups CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] {m : ℕ}

@[expose] def epsMat (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) F :=
  Matrix.of fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => A i' j') j) i

@[simp] theorem epsMat_zero_zero (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) :
    epsMat A 0 0 = 1 := rfl

@[simp] theorem epsMat_zero_succ (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (j : Fin (m + 1)) :
    epsMat A 0 j.succ = 0 := rfl

@[simp] theorem epsMat_succ_zero (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (i : Fin (m + 1)) :
    epsMat A i.succ 0 = 0 := rfl

@[simp] theorem epsMat_succ_succ (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (i j : Fin (m + 1)) :
    epsMat A i.succ j.succ = A i j := rfl

theorem epsMat_one : epsMat (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem epsMat_mul (A B : Matrix (Fin (m + 1)) (Fin (m + 1)) F) :
    epsMat A * epsMat B = epsMat (A * B) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [Matrix.mul_apply]

theorem det_epsMat (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) : (epsMat A).det = A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [Fin.succAbove_zero]
  rw [show (epsMat A).submatrix Fin.succ Fin.succ = A from by ext i j; rfl]

@[expose] noncomputable def epsHom (m : ℕ) (F : Type) [Field F] :
    SpecialLinearGroup (Fin (m + 1)) F →* SpecialLinearGroup (Fin (m + 2)) F where
  toFun A := ⟨epsMat (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F), by rw [det_epsMat, A.2]⟩
  map_one' := Subtype.ext (by simp [epsMat_one])
  map_mul' A B := Subtype.ext (by
    show epsMat ((A * B : SpecialLinearGroup (Fin (m + 1)) F) : Matrix (Fin (m + 1)) _ F) =
      epsMat (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * epsMat (B : Matrix (Fin (m + 1)) _ F)
    rw [epsMat_mul, SpecialLinearGroup.coe_mul])

theorem coe_epsHom (A : SpecialLinearGroup (Fin (m + 1)) F) :
    ((epsHom m F A : SpecialLinearGroup (Fin (m + 2)) F) : Matrix (Fin (m + 2)) (Fin (m + 2)) F) =
      epsMat (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := rfl

theorem epsMat_mulVec_e0 (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) :
    epsMat A *ᵥ (Pi.single 0 1 : Fin (m + 2) → F) = Pi.single 0 1 := by
  funext i
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp
  · simp [Fin.succ_ne_zero]

theorem epsHom_fix_e0 (A : SpecialLinearGroup (Fin (m + 1)) F) :
    ((epsHom m F A : SpecialLinearGroup (Fin (m + 2)) F) : Matrix (Fin (m + 2)) (Fin (m + 2)) F)
      *ᵥ (Pi.single 0 1 : Fin (m + 2) → F) = Pi.single 0 1 := by
  rw [coe_epsHom]
  exact epsMat_mulVec_e0 _

theorem epsHom_mem_unitriangular {u : SpecialLinearGroup (Fin (m + 1)) F}
    (hu : u ∈ unitriangular (m + 1) F) : epsHom m F u ∈ unitriangular (m + 2) F := by
  rw [mem_unitriangular] at hu ⊢
  rw [coe_epsHom]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · exact absurd hji (Fin.not_lt_zero _)
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · simp
      · rw [epsMat_succ_succ]
        exact hu.1 i' j' (Fin.succ_lt_succ_iff.1 hji)
  · refine Fin.cases ?_ (fun i' => ?_) i
    · simp
    · rw [epsMat_succ_succ]
      exact hu.2 i'

theorem mul_epsMat_zero (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F)
    (B' : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (i : Fin (m + 2)) :
    (g * epsMat B') i 0 = g i 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp

theorem mul_epsMat_succ (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F)
    (B' : Matrix (Fin (m + 1)) (Fin (m + 1)) F) (i : Fin (m + 2)) (j : Fin (m + 1)) :
    (g * epsMat B') i j.succ = ∑ k : Fin (m + 1), g i k.succ * B' k j := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp

theorem exists_unitriangular_of_fix (g : SpecialLinearGroup (Fin (m + 2)) F)
    (hg : (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *ᵥ (Pi.single 0 1 : Fin (m + 2) → F) =
      Pi.single 0 1) :
    ∃ A : SpecialLinearGroup (Fin (m + 1)) F,
      g * (epsHom m F A)⁻¹ ∈ unitriangular (m + 2) F := by
  have hcol : ∀ i, (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) i 0 = if i = 0 then 1 else 0 := by
    intro i
    have := congrFun hg i
    simpa [Pi.single_apply] using this
  set Ag : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
    (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F).submatrix Fin.succ Fin.succ with hAg
  have hdet : Ag.det = 1 := by
    have h1 := g.2
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ] at h1
    simpa [hcol, Fin.succAbove_zero] using h1
  refine ⟨⟨Ag, hdet⟩, ?_⟩
  set A : SpecialLinearGroup (Fin (m + 1)) F := ⟨Ag, hdet⟩ with hA
  rw [← map_inv]
  set B : Matrix (Fin (m + 1)) (Fin (m + 1)) F := ((A⁻¹ : SpecialLinearGroup (Fin (m + 1)) F) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) F) with hB
  have hAB : Ag * B = 1 := by
    have h := congrArg (fun x : SpecialLinearGroup (Fin (m + 1)) F =>
      (x : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) (mul_inv_cancel A)
    simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_one] at h
    exact h
  have hmat : ((g * epsHom m F A⁻¹ : SpecialLinearGroup (Fin (m + 2)) F) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) F) =
      (g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) * epsMat B := rfl
  rw [mem_unitriangular, hmat]
  have hsucc : ∀ i j : Fin (m + 1), ((g : Matrix (Fin (m + 2)) (Fin (m + 2)) F) *
      epsMat B) i.succ j.succ = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j := by
    intro i j
    rw [mul_epsMat_succ, ← hAB, Matrix.mul_apply]
    rfl
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · exact absurd hji (Fin.not_lt_zero _)
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · rw [mul_epsMat_zero, hcol]
        simp [Fin.succ_ne_zero]
      · rw [hsucc]
        exact one_apply_ne (ne_of_gt (Fin.succ_lt_succ_iff.1 hji))
  · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · rw [mul_epsMat_zero, hcol]
      simp
    · rw [hsucc]
      exact one_apply_eq i'

end CFSG.CGT.T75N
