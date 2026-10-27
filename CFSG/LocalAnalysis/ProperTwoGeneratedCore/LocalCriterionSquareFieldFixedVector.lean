module

public import Mathlib.FieldTheory.Finite.Basic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFixedBasis
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

universe u

open scoped MatrixGroups

variable {F : Type u} [Field F]

abbrev nonzeroVectors (F : Type u) [Field F] := {v : Fin 2 → F // v ≠ 0}

instance nonzeroVectorAction (A : Subgroup SL(2, F)) : MulAction A (nonzeroVectors F) where
  smul a v := ⟨(a : SL(2, F)) • (v : Fin 2 → F),
    (smul_ne_zero_iff_ne (a : SL(2, F))).mpr v.2⟩
  one_smul v := by apply Subtype.ext; exact one_smul _ _
  mul_smul a b v := by apply Subtype.ext; exact mul_smul _ _ _

theorem nonzeroVectors_card [Finite F] :
    Nat.card (nonzeroVectors F) = Nat.card F ^ 2 - 1 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun v : Fin 2 → F => v = 0),
    Fintype.card_subtype_eq]
  simp [Nat.card_eq_fintype_card]

theorem nonzeroVectors_card_odd [Finite F] [CharP F 2] :
    ¬2 ∣ Nat.card (nonzeroVectors F) := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨n, _hp, hn⟩ := FiniteField.card F 2
  have hdiv : 2 ∣ Nat.card F := by
    rw [← Fintype.card_eq_nat_card, hn]
    exact dvd_pow_self 2 n.ne_zero
  have hdiv2 : 2 ∣ Nat.card F ^ 2 := hdiv.trans (dvd_pow_self _ (by decide : 2 ≠ 0))
  have hpos : 0 < Nat.card F ^ 2 := pow_pos Nat.card_pos 2
  rw [nonzeroVectors_card]
  omega

theorem pgroup_sl2_common_fixed_vector [Finite F] [CharP F 2]
    (A : Subgroup SL(2, F)) (hA : IsPGroup 2 A) :
    ∃ v : Fin 2 → F, v ≠ 0 ∧ ∀ a ∈ A, (a : SL(2, F)) • v = v := by
  obtain ⟨v, hv⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card
    (nonzeroVectors F) nonzeroVectors_card_odd
  refine ⟨v, v.2, ?_⟩
  intro a ha
  exact congrArg (fun w : nonzeroVectors F => (w : Fin 2 → F)) (hv (⟨a, ha⟩ : A))

theorem exists_sl2_first_column (v : Fin 2 → F) (hv : v ≠ 0) :
    ∃ x : SL(2, F), x • (Pi.single 0 1 : Fin 2 → F) = v := by
  classical
  by_cases hv0 : v 0 = 0
  · have hv1 : v 1 ≠ 0 := by
      intro h
      apply hv
      ext i
      fin_cases i <;> assumption
    let x : SL(2, F) := ⟨!![0, -(v 1)⁻¹; v 1, 0], by
      simp [Matrix.det_fin_two, hv1]⟩
    refine ⟨x, ?_⟩
    change Matrix.mulVec (x : Matrix (Fin 2) (Fin 2) F) (Pi.single 0 1) = v
    rw [Matrix.mulVec_single_one]
    ext i
    fin_cases i <;> simp [x, hv0]
  · let x : SL(2, F) := ⟨!![v 0, 0; v 1, (v 0)⁻¹], by
      simp [Matrix.det_fin_two, hv0]⟩
    refine ⟨x, ?_⟩
    change Matrix.mulVec (x : Matrix (Fin 2) (Fin 2) F) (Pi.single 0 1) = v
    rw [Matrix.mulVec_single_one]
    ext i
    fin_cases i <;> simp [x]

end CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
