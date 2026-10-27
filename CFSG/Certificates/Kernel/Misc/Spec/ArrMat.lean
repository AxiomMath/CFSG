module

public import CFSG.LieType.Multipliers.G24Data

public section

namespace CFSG.KC.Misc.Spec

open CFSG.LieType.Multipliers.G24

@[expose] def wordProd {α : Type*} {n : Type*} {R : Type*} [Fintype n] [DecidableEq n]
    [NonUnitalNonAssocSemiring R] [One R] (F : α → Matrix n n R) (w : List α) : Matrix n n R :=
  w.foldr (fun l A => F l * A) 1

theorem mulArr_eq_ofMat {R : Type*} [Semiring R] (n : ℕ) (A B : Array (Array R)) :
    mulArr n A B = ofMat (toMat n A * toMat n B) := rfl

theorem foldr_mulArr {R α : Type*} [Semiring R] (n : ℕ) (F : α → Array (Array R)) (w : List α) :
    w.foldr (fun l A => mulArr n (F l) A) (ofMat (1 : Matrix (Fin n) (Fin n) R)) =
      ofMat (wordProd (fun l => toMat n (F l)) w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.foldr_cons, ih, mulArr_eq_ofMat, toMat_ofMat]
    rfl

theorem ofMat_toMat {R : Type*} [Semiring R] (n : ℕ) (A : Array (Array R)) (h1 : A.size = n)
    (h2 : ∀ r ∈ A.toList, r.size = n) : ofMat (toMat n A) = A := by
  apply Array.ext
  · simp [ofMat, h1]
  · intro i hi1 hi2
    have hi : i < n := by simpa [ofMat] using hi1
    have hrow : A[i].size = n := h2 _ (by simp)
    apply Array.ext
    · simp [ofMat, hrow]
    · intro j hj1 hj2
      have hj : j < n := by simpa [ofMat] using hj1
      simp [ofMat, toMat, Array.getD, hi, hj, h1, hrow]

end CFSG.KC.Misc.Spec

end
