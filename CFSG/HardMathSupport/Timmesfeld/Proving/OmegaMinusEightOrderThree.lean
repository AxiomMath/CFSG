module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open Matrix
open scoped commutatorElement

namespace MinusEightOrderThree

abbrev ι8 : Type := Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2

abbrev Q8 : (ι8 → ZMod 2) → ZMod 2 := StatedQuadMinus 4 (ZMod 2) 1 1

@[expose] def idx8 : ι8 → Fin 8
  | .inl i => ![0, 1, 2] i
  | .inr (.inl i) => ![3, 4, 5] i
  | .inr (.inr i) => ![6, 7] i

@[expose] def mat8 (r : Fin 8 → Fin 8 → ZMod 2) : Matrix ι8 ι8 (ZMod 2) :=
  Matrix.of fun i j => r (idx8 i) (idx8 j)

@[expose] def R1 : Matrix ι8 ι8 (ZMod 2) :=
  mat8 fun i j => if i = j ∨ (i = 7 ∧ j = 6) then 1 else 0

@[expose] def R2 : Matrix ι8 ι8 (ZMod 2) :=
  mat8 fun i j => if i = j ∨ (i = 6 ∧ j = 7) then 1 else 0

theorem R1_isometry : ∀ v : ι8 → ZMod 2, Q8 (R1 *ᵥ v) = Q8 v := by decide +kernel

theorem R2_isometry : ∀ v : ι8 → ZMod 2, Q8 (R2 *ᵥ v) = Q8 v := by decide +kernel

theorem R1_mul_R1 : R1 * R1 = 1 := by decide +kernel

theorem R2_mul_R2 : R2 * R2 = 1 := by decide +kernel

@[expose] def X1 : GL ι8 (ZMod 2) := Units.mk R1 R1 R1_mul_R1 R1_mul_R1

@[expose] def X2 : GL ι8 (ZMod 2) := Units.mk R2 R2 R2_mul_R2 R2_mul_R2

theorem commutator_pow_three : (R1 * R2 * R1 * R2) ^ 3 = 1 := by decide +kernel

theorem commutator_ne_one : R1 * R2 * R1 * R2 ≠ 1 := by decide +kernel

theorem orderOf_commutatorElement_X : orderOf ⁅X1, X2⁆ = 3 := by
  have hval : ((⁅X1, X2⁆ : GL ι8 (ZMod 2)) : Matrix ι8 ι8 (ZMod 2)) = R1 * R2 * R1 * R2 := by
    simp [commutatorElement_def, X1, X2]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
  · exact Units.ext (by rw [Units.val_pow_eq_pow_val, hval, Units.val_one]; exact commutator_pow_three)
  · intro h
    apply commutator_ne_one
    rw [← hval, h, Units.val_one]

theorem mem_isometry_X1 : X1 ∈ {A : GL ι8 (ZMod 2) | ∀ v, Q8 ((A : Matrix ι8 ι8 (ZMod 2)) *ᵥ v) = Q8 v} :=
  R1_isometry

theorem mem_isometry_X2 : X2 ∈ {A : GL ι8 (ZMod 2) | ∀ v, Q8 ((A : Matrix ι8 ι8 (ZMod 2)) *ᵥ v) = Q8 v} :=
  R2_isometry

theorem exists_orderOf_three_statedOmega_quadMinus_four :
    ∃ B ∈ StatedOmega (StatedQuadMinus 4 (ZMod 2) 1 1), orderOf B = 3 := by
  refine ⟨⁅X1, X2⁆, ?_, orderOf_commutatorElement_X⟩
  unfold StatedOmega
  exact Subgroup.commutator_mem_commutator (Subgroup.subset_closure mem_isometry_X1)
    (Subgroup.subset_closure mem_isometry_X2)

theorem three_dvd_card_statedOmega_quadMinus_four :
    3 ∣ Nat.card ↥(StatedOmega (StatedQuadMinus 4 (ZMod 2) 1 1)) := by
  obtain ⟨B, hB, hord⟩ := exists_orderOf_three_statedOmega_quadMinus_four
  have h := orderOf_dvd_natCard (⟨B, hB⟩ : ↥(StatedOmega (StatedQuadMinus 4 (ZMod 2) 1 1)))
  rwa [Subgroup.orderOf_mk, hord] at h

end MinusEightOrderThree

end CFSG.HardMathSupport.Timmesfeld.Proving

end
