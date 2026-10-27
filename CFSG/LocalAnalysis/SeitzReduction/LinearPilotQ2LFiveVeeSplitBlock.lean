module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {F : Type*} [Field F]

@[expose] def veeBlockFive (r : Fin 4 → F) (A : Matrix (Fin 4) (Fin 4) F) :
    Matrix (Fin 5) (Fin 5) F :=
  Matrix.of (Fin.cases (Fin.cases 1 r) fun k => Fin.cases 0 (A k))

@[simp] theorem veeBlockFive_zero_zero (r : Fin 4 → F) (A : Matrix (Fin 4) (Fin 4) F) :
    veeBlockFive r A 0 0 = 1 := rfl

@[simp] theorem veeBlockFive_zero_succ (r : Fin 4 → F) (A : Matrix (Fin 4) (Fin 4) F)
    (j : Fin 4) : veeBlockFive r A 0 j.succ = r j := rfl

@[simp] theorem veeBlockFive_succ_zero (r : Fin 4 → F) (A : Matrix (Fin 4) (Fin 4) F)
    (i : Fin 4) : veeBlockFive r A i.succ 0 = 0 := rfl

@[simp] theorem veeBlockFive_succ_succ (r : Fin 4 → F) (A : Matrix (Fin 4) (Fin 4) F)
    (i j : Fin 4) : veeBlockFive r A i.succ j.succ = A i j := rfl

theorem veeBlockFive_mul (r r' : Fin 4 → F) (A A' : Matrix (Fin 4) (Fin 4) F) :
    veeBlockFive r A * veeBlockFive r' A' = veeBlockFive (r' + r ᵥ* A') (A * A') := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, vecMul, dotProduct]

theorem veeBlockFive_zero_one : veeBlockFive (0 : Fin 4 → F) 1 = 1 := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem veeBlockFive_map {F' : Type*} [Field F'] (f : F →+* F') (r : Fin 4 → F)
    (A : Matrix (Fin 4) (Fin 4) F) :
    (veeBlockFive r A).map f = veeBlockFive (f ∘ r) (A.map f) := by
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j <;>
    simp [Matrix.map_apply]

theorem veeBlockFive_upper {r : Fin 4 → F} {A : Matrix (Fin 4) (Fin 4) F}
    (hA : ∀ i j : Fin 4, j < i → A i j = 0) : ∀ i j : Fin 5, j < i → veeBlockFive r A i j = 0 := by
  intro i j hij
  revert hij
  refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j
  · intro h; exact absurd h (lt_irrefl _)
  · intro h; exact absurd h (Fin.not_lt_zero _)
  · intro _; rfl
  · intro h
    exact hA k l (Fin.succ_lt_succ_iff.1 h)

theorem veeBlockFive_diag {r : Fin 4 → F} {A : Matrix (Fin 4) (Fin 4) F}
    (hA : ∀ i : Fin 4, A i i = 1) : ∀ i : Fin 5, veeBlockFive r A i i = 1 := by
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · exact hA k

theorem veeBlockFive_det {r : Fin 4 → F} {A : Matrix (Fin 4) (Fin 4) F}
    (hA : ∀ i j : Fin 4, j < i → A i j = 0) (hA1 : ∀ i : Fin 4, A i i = 1) :
    (veeBlockFive r A).det = 1 := by
  rw [det_of_isUpperTriangular (fun i j h => veeBlockFive_upper hA i j h)]
  exact Finset.prod_eq_one fun i _ => veeBlockFive_diag hA1 i

@[expose] def veeBlockFiveU (r : Fin 4 → F) (A : unitriangular 4 F) : unitriangular 5 F :=
  ⟨⟨veeBlockFive r ((A : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F),
      veeBlockFive_det A.2.1 A.2.2⟩,
    veeBlockFive_upper A.2.1, veeBlockFive_diag A.2.2⟩

theorem veeBlockFive_lower_eq_zero_iff {r : Fin 4 → F} {A : Matrix (Fin 4) (Fin 4) F}
    (hA : ∀ i j : Fin 4, j < i → A i j = 0) (hA1 : ∀ i : Fin 4, A i i = 1) :
    (∀ i j : Fin 5, 0 < i → i < j → veeBlockFive r A i j = 0) ↔ A = 1 := by
  constructor
  · intro h
    ext k l
    rcases lt_trichotomy k l with hkl | rfl | hkl
    · have h1 := h k.succ l.succ (Fin.succ_pos k) (Fin.succ_lt_succ_iff.2 hkl)
      rw [veeBlockFive_succ_succ] at h1
      rw [h1, Matrix.one_apply_ne hkl.ne]
    · rw [hA1, Matrix.one_apply_eq]
    · rw [hA k l hkl, Matrix.one_apply_ne hkl.ne']
  · rintro rfl i j hi hij
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 (Fin.pos_iff_ne_zero.1 hi)
    obtain ⟨l, rfl⟩ := Fin.exists_succ_eq.2 (Fin.pos_iff_ne_zero.1 (hi.trans hij))
    rw [veeBlockFive_succ_succ, Matrix.one_apply_ne (Fin.succ_lt_succ_iff.1 hij).ne]

end CFSG.SeitzReduction.LinearPilot
