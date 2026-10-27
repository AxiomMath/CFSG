module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeArithmeticBasic

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeArithmetic

inductive DegreeRepresentation where
  | first (i : ℕ)
  | second (q : ℤ) (j : ℕ)
  deriving DecidableEq

@[expose] def representsDegree (b : ℤ) (n : ℚ) : DegreeRepresentation → Prop
  | .first i => 1 ≤ i ∧ i ≤ 3 ∧ n = degreeF i b
  | .second q j => 4 ≤ q ∧ (∃ f : ℕ, q = 2 ^ f) ∧ q ^ 2 = b ∧
      1 ≤ j ∧ j ≤ 3 ∧ n = degreeG j q

theorem fixed_parameter_degree_unique (b : ℤ) (hb : 4 ≤ b)
    (_hbpower : ∃ f : ℕ, b = 2 ^ f) (n : ℚ) :
    {r : DegreeRepresentation | representsDegree b n r}.Subsingleton := by
  intro r hr s hs
  cases r with
  | first i =>
    cases s with
    | first j =>
      have hvalue : degreeF i b = degreeF j b := hr.2.2.symm.trans hs.2.2
      have hij := (degreeF_strictMono b hb).injective hvalue
      exact congrArg DegreeRepresentation.first hij
    | second q j =>
      have hlt := degree_square_parameter_separation q hs.1 i j hr.1 hs.2.2.2.2.1
      rw [hs.2.2.1] at hlt
      rw [← hr.2.2, ← hs.2.2.2.2.2] at hlt
      exact False.elim (lt_irrefl n hlt)
  | second q i =>
    cases s with
    | first j =>
      have hlt := degree_square_parameter_separation q hr.1 j i hs.1 hr.2.2.2.2.1
      rw [hr.2.2.1] at hlt
      rw [← hr.2.2.2.2.2, ← hs.2.2] at hlt
      exact False.elim (lt_irrefl n hlt)
    | second p j =>
      have hq0 : (0 : ℤ) ≤ q := le_trans (by norm_num) hr.1
      have hp0 : (0 : ℤ) ≤ p := le_trans (by norm_num) hs.1
      have hqp : q = p := (sq_eq_sq₀ hq0 hp0).mp (hr.2.2.1.trans hs.2.2.1.symm)
      subst p
      have hvalue : degreeG i q = degreeG j q := hr.2.2.2.2.2.symm.trans hs.2.2.2.2.2
      have hij := (degreeG_strictMono q hr.1).injective hvalue
      exact congrArg (DegreeRepresentation.second q) hij

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeArithmetic
