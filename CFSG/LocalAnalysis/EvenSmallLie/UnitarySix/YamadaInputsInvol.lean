module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInputsLift
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearPureGraph
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearGraphFieldDescent

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaInputs

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ComponentClassification
open scoped MatrixGroups

section FieldFour

variable {F : Type*} [Field F]

theorem charP_two_of_card_four (hF : Nat.card F = 4) : CharP F 2 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  exact finite_field_prime_power_characteristic Nat.prime_two (k := 2) (by norm_num)
    (by rw [hF]; norm_num)

theorem pow_three_eq_one_of_card_four (hF : Nat.card F = 4) {x : F} (hx : x ≠ 0) :
    x ^ 3 = 1 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  have hu : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have := pow_card_eq_one' (G := Fˣ) (x := Units.mk0 x hx)
  rw [hu] at this
  exact congrArg Units.val this

theorem eq_one_of_sq_eq_one_of_charTwo [CharP F 2] {d : F} (hd : d * d = 1) : d = 1 := by
  have h : (d + 1) * (d + 1) = 0 := by
    have : (d + 1) * (d + 1) = d * d + 1 + (2 : F) * d := by ring
    rw [this, hd, CharTwo.two_eq_zero, zero_mul, add_zero, CharTwo.add_self_eq_zero]
  have h1 : d + 1 = 0 := mul_self_eq_zero.mp h
  rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq]
  exact h1

end FieldFour

section Cases

variable {n : ℕ} {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem stdSL_one_zero (A : GL (Fin n) F) :
    stdSL n F A 1 0 = CatalogueBHigherLinearAction.slConjugation n F A := by
  rw [stdSL, map_one, mul_one, pow_zero, mul_one]

omit [Finite F] in
theorem descendAut_conj (g : SL(n, F)) :
    descendAut n F (MulAut.conj g) = MulAut.conj (proj n F g) := by
  ext x
  obtain ⟨y, rfl⟩ := proj_surjective n F x
  rw [descendAut_proj, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem exists_conj_eq_stdSL (hn : 3 ≤ n) (hF : Nat.card F = 4) (A : GL (Fin n) F)
    (h2 : conjAut n F A ^ 2 = 1) :
    ∃ g : SL(n, F), g * g = 1 ∧ stdSL n F A 1 0 = MulAut.conj g := by
  have := charP_two_of_card_four hF
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (K := F) hn (A * A) 1
    (by rw [map_one, mul_one, map_mul, ← sq, h2])
  have hc3 : (c : F) ^ 3 = 1 := pow_three_eq_one_of_card_four hF c.ne_zero
  set M : Matrix (Fin n) (Fin n) F := (c : F) • (A : Matrix (Fin n) (Fin n) F) with hM
  have hAA : (A : Matrix (Fin n) (Fin n) F) * A = scalar (Fin n) (c : F) := by
    rw [← Units.val_mul, ← hc, GeneralLinearGroup.coe_scalar]
  have hMM : M * M = 1 := by
    rw [hM, smul_mul_smul_comm, hAA, scalar_apply, ← diagonal_smul, ← diagonal_one]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← hc3]
    ring
  have hdet : M.det = 1 :=
    eq_one_of_sq_eq_one_of_charTwo (by rw [← det_mul, hMM, det_one])
  set g : SL(n, F) := ⟨M, hdet⟩
  refine ⟨g, Subtype.ext hMM, eq_of_descendAut_eq hn ?_⟩
  rw [descendAut_stdSL, map_one, mul_one, pow_zero, mul_one, descendAut_conj, ← conjAut_toGL]
  have hg : SpecialLinearGroup.toGL g = GeneralLinearGroup.scalar (Fin n) c * A := by
    ext i j
    rw [SpecialLinearGroup.coe_GL_coe_matrix, Units.val_mul, GeneralLinearGroup.coe_scalar,
      scalar_apply, diagonal_mul]
    rfl
  rw [hg, map_mul, conjAut_scalar, one_mul]

theorem pow_two_half : (2 : ℕ) ^ (2 / 2) = 2 := by norm_num

theorem stdSL_cases (hn : 3 ≤ n) (hF : Nat.card F = 4) (A : GL (Fin n) F) (σ : F ≃+* F)
    {ε : ℕ} (hε : ε ≤ 1) (h2 : (conjAut n F A * fieldAut n F σ * dualAut n F ^ ε) ^ 2 = 1) :
    (ε = 0 ∧ σ = 1 ∧ ∃ g : SL(n, F), g * g = 1 ∧ stdSL n F A σ ε = MulAut.conj g) ∨
    (ε = 1 ∧ σ = 1 ∧ ∃ H C : GL (Fin n) F, ((C : Matrix (Fin n) (Fin n) F) = 1 ∨
        ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) F) = blockSwapJ n r) ∧
      stdSL n F A σ ε = stdSL n F H 1 0 * stdSL n F C 1 1 * (stdSL n F H 1 0)⁻¹) ∨
    (ε = 0 ∧ σ ≠ 1 ∧ (∀ x, σ x = x ^ 2) ∧ ∃ H : GL (Fin n) F,
      stdSL n F A σ ε = stdSL n F H 1 0 * stdSL n F 1 σ 0 * (stdSL n F H 1 0)⁻¹) ∨
    (ε = 1 ∧ σ ≠ 1 ∧ (∀ x, σ x = x ^ 2) ∧ ∃ H : GL (Fin n) F,
      stdSL n F A σ ε = stdSL n F H 1 0 * stdSL n F 1 σ 1 * (stdSL n F H 1 0)⁻¹) := by
  have hK : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  have hd : ∀ (H : GL (Fin n) F) (β : MulAut SL(n, F)),
      descendAut n F (stdSL n F H 1 0 * β * (stdSL n F H 1 0)⁻¹) =
        conjAut n F H * descendAut n F β * (conjAut n F H)⁻¹ := fun H β => by
    rw [map_mul, map_mul, map_inv, descendAut_stdSL, map_one, mul_one, pow_zero, mul_one]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at h2
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at h2
      exact Or.inl ⟨rfl, rfl, by
        rw [show stdSL n F A 1 0 = stdSL n F A 1 0 from rfl]
        exact exists_conj_eq_stdSL hn hF A h2⟩
    · obtain ⟨-, hσx, H, hH⟩ :=
        even_linear_field_involution_descent (f := 2) (by norm_num) hK hn A σ hσ h2
      refine Or.inr (Or.inr (Or.inl ⟨rfl, hσ, fun x => by rw [hσx, pow_two_half], H,
        eq_of_descendAut_eq hn ?_⟩))
      rw [hd, descendAut_stdSL, descendAut_stdSL, map_one, one_mul, pow_zero, mul_one,
        mul_one, hH]
  · rw [pow_one] at h2
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at h2
      obtain ⟨-, ⟨H, C, -, hHC, hC⟩, -⟩ :=
        even_linear_pure_graph_involution_normal_forms (f := 2) (by norm_num) hK hn A h2
      have hC' : (C : Matrix (Fin n) (Fin n) F) = 1 ∨
          ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) F) = blockSwapJ n r := by
        rcases hC with h | ⟨r, hr, hr', -⟩
        · exact Or.inl h.1
        · exact Or.inr ⟨r, hr, hr'⟩
      refine Or.inr (Or.inl ⟨rfl, rfl, H, C, hC', eq_of_descendAut_eq hn ?_⟩)
      rw [hd, descendAut_stdSL, descendAut_stdSL, map_one, mul_one, mul_one, pow_one]
      exact hHC
    · obtain ⟨-, hσx, H, hH⟩ :=
        linear_graph_field_involution_descent Nat.prime_two (f := 2) (by norm_num) hK hn A σ hσ
          h2
      refine Or.inr (Or.inr (Or.inr ⟨rfl, hσ, fun x => by rw [hσx, pow_two_half], H,
        eq_of_descendAut_eq hn ?_⟩))
      rw [hd, descendAut_stdSL, descendAut_stdSL, map_one, one_mul, pow_one]
      exact hH

end Cases

end CFSG.EvenSmallLie.UnitarySix.YamadaInputs
