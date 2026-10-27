
module

public import Certificates.Data.E27.Fi22S0
public import CFSG.Open.LocalVocabulary
public import CFSG.Sporadic.Fi22.Simple

@[expose] public section

namespace CFSG.HardMathSupport.Foote.E27.Fi22S0

open CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.S0 CFSG.Sporadic.Fi22.Native CFSG.F3.Native
  CFSG.HardMathSupport.Foote.E27 Subgroup

section Certificates

noncomputable abbrev matJ (g : J) : Matrix (Fin 77) (Fin 77) (ZMod 3) :=
  ((g : GL (Fin 77) (ZMod 3)) : Matrix (Fin 77) (Fin 77) (ZMod 3))

theorem matJ_mul (g h : J) : matJ (g * h) = matJ g * matJ h := rfl

theorem matJ_one : matJ (1 : J) = 1 := rfl

theorem matJ_injective : Function.Injective (matJ : J → _) := fun g h e =>
  Subtype.ext (Units.ext e)

noncomputable def regJ (k : ℕ) : J :=
  if h : 3 ≤ k ∧ (ops[k - 3]!).1 < k ∧ (ops[k - 3]!).2 < k then
    regJ (ops[k - 3]!).1 * regJ (ops[k - 3]!).2
  else if k = 0 then a else if k = 1 then b else if k = 2 then b⁻¹ else 1
termination_by k
decreasing_by
  all_goals first | exact h.2.1 | exact h.2.2

noncomputable def gJ (j : ℕ) : J := regJ (gens[j]!)

theorem gJ_eq (j : ℕ) : gJ j = regJ (gens[j]!) := by unfold gJ; rfl

theorem regJ_succ {k : ℕ} (h : 3 ≤ k ∧ (ops[k - 3]!).1 < k ∧ (ops[k - 3]!).2 < k) :
    regJ k = regJ (ops[k - 3]!).1 * regJ (ops[k - 3]!).2 := by
  rw [regJ]; simp [h]

theorem regJ_zero : regJ 0 = a := by rw [regJ]; simp

theorem regJ_one : regJ 1 = b := by rw [regJ]; simp

theorem regJ_two : regJ 2 = b⁻¹ := by rw [regJ]; simp

theorem card_J_eq : Nat.card J = 64561751654400 := by
  rw [← Nat.card_congr fi22EquivJ.toEquiv]; exact card_Fi22

theorem finite_J : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J_eq]; norm_num)

theorem factorization_J : (Nat.card J).factorization 3 = 9 := by
  rw [card_J_eq]
  have h : (64561751654400 : ℕ) = 3 ^ 9 * (2 ^ 17 * 5 ^ 2 * 7 * 11 * 13) := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

end Certificates

end CFSG.HardMathSupport.Foote.E27.Fi22S0

namespace CFSG.HardMathSupport.Foote.E27

end CFSG.HardMathSupport.Foote.E27
