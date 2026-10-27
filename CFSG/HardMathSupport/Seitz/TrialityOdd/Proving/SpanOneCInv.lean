module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

open Polynomial

theorem not_quadratic_of_finrank_three {F K : Type*} [Field F] [Field K] [Algebra F K]
    (h3 : Module.finrank F K = 3) {c : K} (hc : c ∉ (algebraMap F K).range)
    {a b d : F} (hb : b ≠ 0)
    (hq : algebraMap F K a * c + algebraMap F K b * c ^ 2 + algebraMap F K d = 0) : False := by
  have : Module.Finite F K := Module.finite_of_finrank_pos (by omega)
  have hint : IsIntegral F c := Algebra.IsIntegral.isIntegral c
  have htower := Module.finrank_mul_finrank F (IntermediateField.adjoin F {c}) K
  rw [h3] at htower
  have hdvd : Module.finrank F (IntermediateField.adjoin F {c}) ∣ 3 := Dvd.intro _ htower
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3'
  · have hbot : IntermediateField.adjoin F {c} = ⊥ :=
      (IntermediateField.finrank_eq_one_iff).1 h1
    have hmem : c ∈ IntermediateField.adjoin F {c} :=
      IntermediateField.mem_adjoin_simple_self F c
    rw [hbot, IntermediateField.mem_bot] at hmem
    exact hc hmem
  · have hdeg : (minpoly F c).natDegree = 3 := by
      rw [← IntermediateField.adjoin.finrank hint]
      exact h3'
    have hpne : (C b * X ^ 2 + C a * X + C d : F[X]) ≠ 0 := by
      intro h
      have hcoeff := congrArg (fun q : F[X] => q.coeff 2) h
      simp [hb] at hcoeff
    have hev : aeval c (C b * X ^ 2 + C a * X + C d : F[X]) = 0 := by
      simp only [map_add, map_mul, aeval_C, aeval_X, map_pow]
      linear_combination hq
    have hdl := minpoly.degree_le_of_ne_zero (A := F) c hpne hev
    have hnd : (minpoly F c).natDegree ≤ (C b * X ^ 2 + C a * X + C d : F[X]).natDegree :=
      Polynomial.natDegree_le_natDegree hdl
    have hq2 : (C b * X ^ 2 + C a * X + C d : F[X]).natDegree ≤ 2 := natDegree_quadratic_le
    omega

end CFSG.HardMathSupport.Seitz.TrialityOdd.Proving

end
