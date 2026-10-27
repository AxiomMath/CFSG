module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open Equiv

private instance instDecEqPermFin5 : DecidableEq (Perm (Fin 5)) := fun a b =>
  decidable_of_iff (∀ i : Fin 5, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 2000 in
theorem s5_exists_three_not_normalizing : ∀ π : Perm (Fin 5), (π * π = 1 ∧ Perm.sign π ≠ 1) →
    ∀ a : Perm (Fin 5), (Perm.sign a = 1 ∧ a * a = 1 ∧ a ≠ 1) →
    ∀ b : Perm (Fin 5), (Perm.sign b = 1 ∧ b * b = 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a ∧
      (π * a * π⁻¹ = a ∨ π * a * π⁻¹ = b ∨ π * a * π⁻¹ = a * b) ∧
      (π * b * π⁻¹ = a ∨ π * b * π⁻¹ = b ∨ π * b * π⁻¹ = a * b)) →
    ∃ c : Perm (Fin 5), Perm.sign c = 1 ∧ c * c * c = 1 ∧ c ≠ 1 ∧ π * c = c * π ∧
      ¬ ((c * a * c⁻¹ = a ∨ c * a * c⁻¹ = b ∨ c * a * c⁻¹ = a * b) ∧
        (c * b * c⁻¹ = a ∨ c * b * c⁻¹ = b ∨ c * b * c⁻¹ = a * b)) := by
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 2000 in
theorem s5_exists_three_normalizing :
    ∀ a : Perm (Fin 5), (Perm.sign a = 1 ∧ a * a = 1 ∧ a ≠ 1) →
    ∀ b : Perm (Fin 5), (Perm.sign b = 1 ∧ b * b = 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a) →
    ∃ d : Perm (Fin 5), Perm.sign d = 1 ∧ d * d * d = 1 ∧ d ≠ 1 ∧
      (d * a * d⁻¹ = a ∨ d * a * d⁻¹ = b ∨ d * a * d⁻¹ = a * b) ∧
      (d * b * d⁻¹ = a ∨ d * b * d⁻¹ = b ∨ d * b * d⁻¹ = a * b) := by
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 2000 in
theorem s5_exists_mul_involution : ∀ π : Perm (Fin 5), Perm.sign π ≠ 1 →
    ∀ a : Perm (Fin 5), (Perm.sign a = 1 ∧ a * a = 1 ∧ a ≠ 1) →
    ∀ b : Perm (Fin 5), (Perm.sign b = 1 ∧ b * b = 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a ∧
      (π * a * π⁻¹ = a ∨ π * a * π⁻¹ = b ∨ π * a * π⁻¹ = a * b) ∧
      (π * b * π⁻¹ = a ∨ π * b * π⁻¹ = b ∨ π * b * π⁻¹ = a * b) ∧
      (π * π = 1 ∨ π * π = a ∨ π * π = b ∨ π * π = a * b)) →
    (π * π = 1 ∨ π * a * (π * a) = 1 ∨ π * b * (π * b) = 1 ∨
      π * (a * b) * (π * (a * b)) = 1) := by
  decide +kernel

end CFSG.ProperTwoGeneratedCore.Lemma37
