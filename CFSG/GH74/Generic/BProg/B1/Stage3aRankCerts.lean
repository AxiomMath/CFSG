module

public import CFSG.GH74.Generic.Certificates

public section

namespace CFSG.GH74.Generic.BProg.B1

open CFSG CFSG.GH74 CFSG.GH74.Generic Subgroup

theorem rankCertified_of_isElementaryAbelian {X : Type} [Group X] (S : Subgroup X)
    (hE : IsElementaryAbelian 2 ↥S) {r : ℕ} (hcard : 2 ^ r < Nat.card ↥S) : RankCertified X r := by
  have : Finite ↥S := Nat.finite_of_card_ne_zero (lt_of_le_of_lt (Nat.zero_le _) hcard).ne'
  refine ⟨↥S, ↥S, inferInstance, inferInstance, inferInstance, S.subtype, MonoidHom.id _,
    Function.surjective_id, fun a b => mul_comm' a b, fun a => ?_, hcard, ?_⟩
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.exponent_dvd_p a
  · rw [Subgroup.ker_subtype]
    exact bot_le

theorem rankCertified_two_of_three_involutions {X : Type} [Group X] {a b c : X}
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : a * b = b * a) (hac : a * c = c * a) (hbc : b * c = c * b)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1) (hab1 : a ≠ b) (hac1 : a ≠ c) (hbc1 : b ≠ c)
    (habc : a * b ≠ c) : RankCertified X 2 := by
  have hab' : a * b ≠ 1 := fun h => hab1 (by
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hb])
  have hac' : a * c ≠ 1 := fun h => hac1 (by
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hc])
  have hbc' : b * c ≠ 1 := fun h => hbc1 (by
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hc])
  have habc' : a * (b * c) ≠ 1 := fun h => habc (by
    rw [← mul_assoc] at h
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hc])
  refine rankCertified_of_commuting_involutions (r := 3) ![a, b, c] ?_ ?_ ?_ (by norm_num)
  · intro i
    fin_cases i <;> simp [sq, ha, hb, hc]
  · have h1 : Commute a b := hab
    have h2 : Commute a c := hac
    have h3 : Commute b c := hbc
    intro i j
    fin_cases i <;> fin_cases j <;> first
      | exact Commute.refl _
      | exact h1
      | exact h2
      | exact h3
      | exact h1.symm
      | exact h2.symm
      | exact h3.symm
  · intro e he h
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h
    have hk : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
    rcases hk (e 0) with h0 | h0 <;> rcases hk (e 1) with h1 | h1 <;>
      rcases hk (e 2) with h2 | h2 <;> simp [h0, h1, h2] at h
    all_goals first
      | exact ha1 h
      | exact hb1 h
      | exact hc1 h
      | exact hab' h
      | exact hac' h
      | exact hbc' h
      | exact habc' h
      | exact he (funext fun i => by fin_cases i <;> simp [h0, h1, h2])

end CFSG.GH74.Generic.BProg.B1
