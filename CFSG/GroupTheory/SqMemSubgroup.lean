module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory

variable {Γ : Type*} [Group Γ]

def sqMemSubgroup (I : Subgroup Γ)
    (hI : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ I) : Subgroup Γ where
  carrier := {a | a ^ 2 ∈ I}
  one_mem' := by simpa using I.one_mem
  mul_mem' := by
    intro a b ha hb
    change (a * b) ^ 2 ∈ I
    have hcomm : a⁻¹ * b * a * b⁻¹ ∈ I := by
      simpa using hI a⁻¹ b
    have h : (a * b) ^ 2 = a ^ 2 * (a⁻¹ * b * a * b⁻¹) * b ^ 2 := by
      rw [pow_two, pow_two, pow_two]
      group
    rw [h]
    exact I.mul_mem (I.mul_mem ha hcomm) hb
  inv_mem' := by
    intro a ha
    change a⁻¹ ^ 2 ∈ I
    have h : a⁻¹ ^ 2 = (a ^ 2)⁻¹ := by
      group
    rw [h]
    exact I.inv_mem ha

theorem mem_sqMemSubgroup {I : Subgroup Γ}
    (hI : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ I) (a : Γ) :
    a ∈ sqMemSubgroup I hI ↔ a ^ 2 ∈ I :=
  Iff.rfl

end CFSG.GroupTheory
