module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

public section

namespace CFSG.ClassicalInvolution.ModelFacts.MF15

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem neg_one_ne_one_sl (h2 : (2 : F) ≠ 0) : (-1 : SL(2, F)) ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp at this
  apply h2
  linear_combination -this

theorem orderOf_La_eq_four (h2 : (2 : F) ≠ 0) (fr : Frame Q) (A : SL(2, F))
    (hA : (A : Matrix (Fin 2) (Fin 2) F) * A = -1) : orderOf (fr.La A) = 4 := by
  have hA' : A * A = -1 := Subtype.ext (by simpa using hA)
  have h2' : fr.La A ^ 2 = fr.La (-1) := by rw [pow_two, ← map_mul, hA']
  have h4 : fr.La A ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2', ← map_pow, show (-1 : SL(2, F)) ^ 2 = 1 by
      rw [pow_two, neg_mul_neg, one_mul], map_one]
  have hne : ¬ fr.La A ^ 2 = 1 := by
    rw [h2']
    intro h
    exact neg_one_ne_one_sl h2 (fr.La_injective (by rw [h, map_one]))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := fr.La A) (by simpa using hne)
    (by simpa using h4)
  simpa using this

end CFSG.ClassicalInvolution.ModelFacts.MF15
