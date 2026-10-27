module

public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.HardMathSupport.Dickson.Bal207.SU38Reduction

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Uni

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

section Order

variable {e m : ℕ} {E : Type} [Field E] (h₀ : UnitaryFieldData 2 e E)

theorem uni_factorization_card_gramSU (hm : 1 ≤ m) :
    (Nat.card (gramSU h₀ ((1 : GL (Fin m) E) : Matrix (Fin m) (Fin m) E))).factorization 2 =
      e * (m * (m - 1) / 2) := by
  have hB := gramForm_isSymm h₀ (G := (1 : Matrix (Fin m) (Fin m) E)) (by
    rw [Matrix.map_one _ (map_zero h₀.bar) (map_one h₀.bar), transpose_one])
  have hBl := gramForm_separatingLeft h₀ (G := (1 : Matrix (Fin m) (Fin m) E)) (by simp)
  have h1 := (CFSG.LinearGroups.unitary_full_group_order h₀ hB hBl
    (Module.finrank_fin_fun E) hm).2.2.2.2.2.2
  rw [← pow_mul] at h1
  rw [Units.val_one, card_gramSU]
  exact Nat.pow_right_injective le_rfl h1

theorem uni_factorization_card_primeFormP (hm : 1 ≤ m) :
    (Nat.card (primeFormP h₀ ((1 : GL (Fin m) E) : Matrix (Fin m) (Fin m) E))).factorization 2 =
      e * (m * (m - 1) / 2) := by
  have := h₀.finite
  have : Finite (GL (Fin m) E) :=
    Finite.of_injective (fun g : GL (Fin m) E => (g : Matrix (Fin m) (Fin m) E))
      Units.val_injective
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (normOneScalars h₀ (gramSU h₀ ((1 : GL (Fin m) E) : Matrix (Fin m) (Fin m) E)) m)
  rw [CFSG.RankThree.Classical.card_normOneScalars_one h₀ hm] at h3
  have hodd : ¬ 2 ∣ Nat.gcd m (2 ^ e + 1) := fun h2 => by
    have h4 := h2.trans (Nat.gcd_dvd_right _ _)
    have h5 : 2 ∣ 2 ^ e := dvd_pow_self 2 (by have := h₀.one_le; omega)
    omega
  have hpos : Nat.card (primeFormP h₀ ((1 : GL (Fin m) E) : Matrix (Fin m) (Fin m) E)) ≠ 0 :=
    Nat.card_pos.ne'
  have hg0 : Nat.gcd m (2 ^ e + 1) ≠ 0 := (Nat.gcd_pos_of_pos_right _ (Nat.succ_pos _)).ne'
  rw [← uni_factorization_card_gramSU h₀ hm, h3, Nat.factorization_mul hpos hg0,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hodd, add_zero]

end Order

theorem uni_factorization_su38 : (5515776 : ℕ).factorization 2 = 9 := by
  rw [show (5515776 : ℕ) = 2 ^ 9 * 10773 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem uni_card_su38 {X : Type} [Group X] {J : Subgroup X} (hJ : IsSU38Comp J) :
    Nat.card (↥J ⧸ Subgroup.center ↥J) = 5515776 := by
  obtain ⟨e⟩ := KSF4SU3.nonempty_equiv_projSU_of_isLieQuot (isLieQuot_isU3EightIndexTwo hJ)
  rw [Nat.card_congr e.toEquiv, CFSG.PGLModel.card_projSU_three_eight]

section Compare

variable {e m : ℕ} {E : Type} [Field E] (h₀ : UnitaryFieldData 2 e E)

theorem uni_eq_nine_of_card (hm : 1 ≤ m)
    (hc : Nat.card (primeFormP h₀ ((1 : GL (Fin m) E) : Matrix (Fin m) (Fin m) E)) = 5515776) :
    e * (m * (m - 1) / 2) = 9 := by
  rw [← uni_factorization_card_primeFormP h₀ hm, hc, uni_factorization_su38]

theorem uni_nine_le_of_dvd (hm : 1 ≤ m)
    (hc : 5515776 ∣ Nat.card (primeFormP h₀ ((1 : GL (Fin m) E) : Matrix (Fin m) (Fin m) E))) :
    9 ≤ e * (m * (m - 1) / 2) := by
  have := h₀.finite
  have : Finite (GL (Fin m) E) :=
    Finite.of_injective (fun g : GL (Fin m) E => (g : Matrix (Fin m) (Fin m) E))
      Units.val_injective
  have hpos : Nat.card (primeFormP h₀ ((1 : GL (Fin m) E) : Matrix (Fin m) (Fin m) E)) ≠ 0 :=
    Nat.card_pos.ne'
  have h1 := (Nat.factorization_le_iff_dvd (by norm_num) hpos).2 hc 2
  rwa [uni_factorization_su38, uni_factorization_card_primeFormP h₀ hm] at h1

end Compare

theorem uni_choose_two_ge {m : ℕ} (hm : 6 ≤ m) : 15 ≤ m * (m - 1) / 2 := by
  have h1 : 30 ≤ m * (m - 1) := Nat.mul_le_mul hm (by omega : 5 ≤ m - 1)
  generalize m * (m - 1) = k at h1 ⊢
  omega

theorem uni_choose_two_ne_nine (m : ℕ) : m * (m - 1) / 2 ≠ 9 := by
  rcases Nat.lt_or_ge m 6 with hm | hm
  · interval_cases m <;> norm_num
  · have h1 := uni_choose_two_ge hm
    generalize m * (m - 1) / 2 = k at h1 ⊢
    omega

theorem uni_nine_cases {e m : ℕ} (he : e = 1 ∨ e = 3) (h9 : e * (m * (m - 1) / 2) = 9) :
    e = 3 ∧ m = 3 := by
  rcases he with rfl | rfl
  · rw [one_mul] at h9
    exact absurd h9 (uni_choose_two_ne_nine m)
  · refine ⟨rfl, ?_⟩
    rcases Nat.lt_or_ge m 6 with hm | hm
    · interval_cases m <;> omega
    · have h1 := uni_choose_two_ge hm
      generalize m * (m - 1) / 2 = k at h1 h9
      omega

theorem uni_nine_le_cases {e m : ℕ} (he : e = 1 ∨ e = 3) (h9 : 9 ≤ e * (m * (m - 1) / 2)) :
    3 ≤ m ∧ ¬(m = 3 ∧ 2 ^ e = 2) := by
  have hm3 : 3 ≤ m := by
    rcases Nat.lt_or_ge m 3 with hlt | hge
    · have hm : m * (m - 1) / 2 ≤ 1 := by interval_cases m <;> norm_num
      rcases he with rfl | rfl
      · generalize m * (m - 1) / 2 = k at hm h9
        omega
      · generalize m * (m - 1) / 2 = k at hm h9
        omega
    · exact hge
  refine ⟨hm3, fun ⟨hm, h2⟩ => ?_⟩
  subst hm
  rcases he with rfl | rfl
  · norm_num at h9
  · norm_num at h2

end CFSG.HardMathSupport.Dickson.Bal207.Uni

end
