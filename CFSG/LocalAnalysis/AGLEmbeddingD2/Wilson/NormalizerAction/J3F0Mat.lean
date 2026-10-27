module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3GammaWords

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Matrix

@[expose] def matS : List (Matrix (Fin 4) (Fin 4) (ZMod 3)) := [
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 0, 1, 0, 0; 1, 0, 1, 0; 1, 2, 2, 1],
  !![1, 0, 0, 0; 0, 1, 0, 0; 2, 0, 1, 0; 1, 1, 1, 1],
  !![1, 0, 0, 0; 0, 1, 1, 0; 0, 1, 2, 0; 0, 0, 1, 1],
  !![1, 0, 0, 0; 0, 1, 1, 0; 1, 1, 2, 0; 1, 1, 1, 1],
  !![1, 0, 0, 0; 0, 1, 1, 0; 2, 1, 2, 0; 1, 2, 1, 1],
  !![1, 0, 0, 0; 0, 2, 0, 0; 0, 0, 2, 0; 0, 1, 0, 1],
  !![1, 0, 0, 0; 0, 2, 0, 0; 1, 0, 2, 0; 1, 2, 1, 1],
  !![1, 0, 0, 0; 0, 2, 0, 0; 2, 0, 2, 0; 1, 0, 2, 1],
  !![1, 0, 0, 0; 0, 2, 2, 0; 0, 2, 1, 0; 0, 1, 2, 1],
  !![1, 0, 0, 0; 0, 2, 2, 0; 1, 2, 1, 0; 1, 0, 2, 1],
  !![1, 0, 0, 0; 0, 2, 2, 0; 2, 2, 1, 0; 1, 2, 2, 1],
  !![1, 0, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 1, 2, 1],
  !![1, 0, 0, 0; 1, 1, 0, 0; 1, 0, 1, 0; 0, 0, 1, 1],
  !![1, 0, 0, 0; 1, 1, 0, 0; 2, 0, 1, 0; 2, 2, 0, 1],
  !![1, 0, 0, 0; 1, 1, 1, 0; 0, 1, 2, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 1, 1, 1, 0; 1, 1, 2, 0; 0, 1, 0, 1],
  !![1, 0, 0, 0; 1, 1, 1, 0; 2, 1, 2, 0; 2, 2, 0, 1],
  !![1, 0, 0, 0; 1, 2, 0, 0; 0, 0, 2, 0; 0, 0, 1, 1],
  !![1, 0, 0, 0; 1, 2, 0, 0; 1, 0, 2, 0; 0, 1, 2, 1],
  !![1, 0, 0, 0; 1, 2, 0, 0; 2, 0, 2, 0; 2, 2, 0, 1],
  !![1, 0, 0, 0; 1, 2, 2, 0; 0, 2, 1, 0; 0, 1, 0, 1],
  !![1, 0, 0, 0; 1, 2, 2, 0; 1, 2, 1, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 1, 2, 2, 0; 2, 2, 1, 0; 2, 2, 0, 1],
  !![1, 0, 0, 0; 2, 1, 0, 0; 0, 0, 1, 0; 1, 2, 1, 1],
  !![1, 0, 0, 0; 2, 1, 0, 0; 1, 0, 1, 0; 0, 1, 0, 1],
  !![1, 0, 0, 0; 2, 1, 0, 0; 2, 0, 1, 0; 1, 0, 2, 1],
  !![1, 0, 0, 0; 2, 1, 1, 0; 0, 1, 2, 0; 1, 0, 2, 1],
  !![1, 0, 0, 0; 2, 1, 1, 0; 1, 1, 2, 0; 0, 1, 2, 1],
  !![1, 0, 0, 0; 2, 1, 1, 0; 2, 1, 2, 0; 1, 2, 2, 1],
  !![1, 0, 0, 0; 2, 2, 0, 0; 0, 0, 2, 0; 1, 2, 2, 1],
  !![1, 0, 0, 0; 2, 2, 0, 0; 1, 0, 2, 0; 0, 0, 0, 1],
  !![1, 0, 0, 0; 2, 2, 0, 0; 2, 0, 2, 0; 1, 1, 1, 1],
  !![1, 0, 0, 0; 2, 2, 2, 0; 0, 2, 1, 0; 1, 1, 1, 1],
  !![1, 0, 0, 0; 2, 2, 2, 0; 1, 2, 1, 0; 0, 0, 1, 1],
  !![1, 0, 0, 0; 2, 2, 2, 0; 2, 2, 1, 0; 1, 2, 1, 1],
  !![2, 0, 0, 0; 0, 0, 1, 0; 0, 1, 1, 0; 1, 2, 1, 1],
  !![2, 0, 0, 0; 0, 0, 1, 0; 1, 1, 1, 0; 0, 0, 0, 1],
  !![2, 0, 0, 0; 0, 0, 1, 0; 2, 1, 1, 0; 0, 1, 2, 1],
  !![2, 0, 0, 0; 0, 0, 2, 0; 0, 2, 2, 0; 1, 2, 2, 1],
  !![2, 0, 0, 0; 0, 0, 2, 0; 1, 2, 2, 0; 0, 1, 0, 1],
  !![2, 0, 0, 0; 0, 0, 2, 0; 2, 2, 2, 0; 0, 0, 1, 1],
  !![2, 0, 0, 0; 0, 1, 2, 0; 0, 2, 0, 0; 1, 0, 2, 1],
  !![2, 0, 0, 0; 0, 1, 2, 0; 1, 2, 0, 0; 0, 0, 1, 1],
  !![2, 0, 0, 0; 0, 1, 2, 0; 2, 2, 0, 0; 0, 0, 0, 1],
  !![2, 0, 0, 0; 0, 2, 1, 0; 0, 1, 0, 0; 1, 1, 1, 1],
  !![2, 0, 0, 0; 0, 2, 1, 0; 1, 1, 0, 0; 0, 1, 2, 1],
  !![2, 0, 0, 0; 0, 2, 1, 0; 2, 1, 0, 0; 0, 1, 0, 1],
  !![2, 0, 0, 0; 1, 0, 1, 0; 0, 1, 1, 0; 0, 0, 1, 1],
  !![2, 0, 0, 0; 1, 0, 1, 0; 1, 1, 1, 0; 0, 1, 0, 1],
  !![2, 0, 0, 0; 1, 0, 1, 0; 2, 1, 1, 0; 1, 2, 2, 1],
  !![2, 0, 0, 0; 1, 0, 2, 0; 0, 2, 2, 0; 0, 1, 2, 1],
  !![2, 0, 0, 0; 1, 0, 2, 0; 1, 2, 2, 0; 0, 0, 0, 1],
  !![2, 0, 0, 0; 1, 0, 2, 0; 2, 2, 2, 0; 1, 2, 1, 1],
  !![2, 0, 0, 0; 1, 1, 2, 0; 0, 2, 0, 0; 0, 1, 0, 1],
  !![2, 0, 0, 0; 1, 1, 2, 0; 1, 2, 0, 0; 0, 1, 2, 1],
  !![2, 0, 0, 0; 1, 1, 2, 0; 2, 2, 0, 0; 1, 1, 1, 1],
  !![2, 0, 0, 0; 1, 2, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1],
  !![2, 0, 0, 0; 1, 2, 1, 0; 1, 1, 0, 0; 0, 0, 1, 1],
  !![2, 0, 0, 0; 1, 2, 1, 0; 2, 1, 0, 0; 1, 0, 2, 1],
  !![2, 0, 0, 0; 2, 0, 1, 0; 0, 1, 1, 0; 1, 1, 1, 1],
  !![2, 0, 0, 0; 2, 0, 1, 0; 1, 1, 1, 0; 2, 2, 0, 1],
  !![2, 0, 0, 0; 2, 0, 1, 0; 2, 1, 1, 0; 1, 0, 2, 1],
  !![2, 0, 0, 0; 2, 0, 2, 0; 0, 2, 2, 0; 1, 0, 2, 1],
  !![2, 0, 0, 0; 2, 0, 2, 0; 1, 2, 2, 0; 2, 2, 0, 1],
  !![2, 0, 0, 0; 2, 0, 2, 0; 2, 2, 2, 0; 1, 1, 1, 1],
  !![2, 0, 0, 0; 2, 1, 2, 0; 0, 2, 0, 0; 1, 2, 1, 1],
  !![2, 0, 0, 0; 2, 1, 2, 0; 1, 2, 0, 0; 2, 2, 0, 1],
  !![2, 0, 0, 0; 2, 1, 2, 0; 2, 2, 0, 0; 1, 2, 2, 1],
  !![2, 0, 0, 0; 2, 2, 1, 0; 0, 1, 0, 0; 1, 2, 2, 1],
  !![2, 0, 0, 0; 2, 2, 1, 0; 1, 1, 0, 0; 2, 2, 0, 1],
  !![2, 0, 0, 0; 2, 2, 1, 0; 2, 1, 0, 0; 1, 2, 1, 1]]



@[expose] def eqM (A B : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Bool :=
  decide (A 0 0 = B 0 0) && decide (A 0 1 = B 0 1) && decide (A 0 2 = B 0 2) &&
  decide (A 0 3 = B 0 3) && decide (A 1 0 = B 1 0) && decide (A 1 1 = B 1 1) &&
  decide (A 1 2 = B 1 2) && decide (A 1 3 = B 1 3) && decide (A 2 0 = B 2 0) &&
  decide (A 2 1 = B 2 1) && decide (A 2 2 = B 2 2) && decide (A 2 3 = B 2 3) &&
  decide (A 3 0 = B 3 0) && decide (A 3 1 = B 3 1) && decide (A 3 2 = B 3 2) &&
  decide (A 3 3 = B 3 3)

theorem eqM_iff {A B : Matrix (Fin 4) (Fin 4) (ZMod 3)} : eqM A B = true ↔ A = B := by
  constructor
  · intro h
    simp only [eqM, Bool.and_eq_true, decide_eq_true_eq] at h
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all
  · rintro rfl
    simp [eqM]

@[expose] def mulM (A B : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  Matrix.of fun i j => A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j + A i 3 * B 3 j

theorem mulM_eq (A B : Matrix (Fin 4) (Fin 4) (ZMod 3)) : mulM A B = A * B := by
  ext i j
  simp [mulM, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def mulV (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) (v : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  fun i => A i 0 * v 0 + A i 1 * v 1 + A i 2 * v 2 + A i 3 * v 3

theorem mulV_eq (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) (v : Fin 4 → ZMod 3) :
    mulV A v = A *ᵥ v := by
  ext i
  simp [mulV, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

@[expose] def subOne (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  Matrix.of fun i j => A i j - (if i = j then 1 else 0)

theorem subOne_eq (A : Matrix (Fin 4) (Fin 4) (ZMod 3)) : subOne A = A - 1 := by
  ext i j
  simp [subOne, Matrix.one_apply]

@[expose] def nzV (v : Fin 4 → ZMod 3) : Bool :=
  !(decide (v 0 = 0) && decide (v 1 = 0) && decide (v 2 = 0) && decide (v 3 = 0))

theorem nzV_iff {v : Fin 4 → ZMod 3} : nzV v = true ↔ v ≠ 0 := by
  constructor
  · intro h h0
    subst h0
    simp [nzV] at h
  · intro h
    by_contra hh
    have h4 : v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 := by
      have := hh
      simp only [nzV, Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true, Bool.not_not] at this
      tauto
    apply h
    ext i
    fin_cases i
    · exact h4.1
    · exact h4.2.1
    · exact h4.2.2.1
    · exact h4.2.2.2

@[expose] def allV : List (Fin 4 → ZMod 3) :=
  (List.range 3).flatMap fun a0 => (List.range 3).flatMap fun a1 =>
    (List.range 3).flatMap fun a2 => (List.range 3).map fun a3 =>
      ![(a0 : ZMod 3), a1, a2, a3]

theorem mem_allV (v : Fin 4 → ZMod 3) : v ∈ allV := by
  revert v; decide

@[expose] def inS (s : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Bool := matS.any (eqM s)

theorem inS_iff {s : Matrix (Fin 4) (Fin 4) (ZMod 3)} : inS s = true ↔ s ∈ matS := by
  simp only [inS, List.any_eq_true, eqM_iff]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ht
  · intro h; exact ⟨s, h, rfl⟩

@[expose] def matChk : Bool :=
  inS 1 &&
  (List.finRange 6).all (fun i => inS (actMat i)) &&
  matS.all (fun s => matS.all fun t => inS (mulM s t)) &&
  matS.all (fun s => matS.any fun t => eqM (mulM s t) 1) &&
  matS.all (fun s => eqM s 1 || allV.any fun v => nzV (mulV (subOne s) (mulV (subOne s) v)))

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
