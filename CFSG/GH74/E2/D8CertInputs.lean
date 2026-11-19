module

public import CFSG.GH74.E2.SD16Cert
public meta import Mathlib

public section

namespace CFSG.GH74.E2

abbrev D8M : Type := DihedralGroup 4

section Relations

variable {M : Type*} [Group M]

@[expose] def D8RelA (a b : M) : Prop :=
  a ^ 4 = 1 ∧ b ^ 2 = 1 ∧ b * a * b⁻¹ = a⁻¹ ∧ a ^ 2 ≠ 1 ∧ b ≠ 1

end Relations

section Certificate

variable (m : ℕ)

@[expose] def D8CentralPow (c : D8M × QuaternionGroup m) : Prop :=
  ∀ y : D8M × QuaternionGroup m, y * c ^ m = c ^ m * y

@[expose] def D8Search4 (a b c : D8M × QuaternionGroup m) : Prop :=
  ∀ d : D8M × QuaternionGroup m, RelC m a b c d → False

@[expose] def D8Search3 (t₀ a b : D8M × QuaternionGroup m) : Prop :=
  ∀ c : D8M × QuaternionGroup m, RelB m a b c → D8CentralPow m c → c ^ m ≠ t₀ → D8Search4 m a b c

@[expose] def D8Search2 (t₀ a : D8M × QuaternionGroup m) : Prop :=
  ∀ b : D8M × QuaternionGroup m, D8RelA a b → D8Search3 m t₀ a b

@[expose] def D8SearchOK (t₀ : D8M × QuaternionGroup m) : Prop :=
  ∀ a : D8M × QuaternionGroup m, a ^ 4 = 1 → D8Search2 m t₀ a

end Certificate

section Instances

@[expose] def d8c (m : ℕ) [NeZero m] : D8M × QuaternionGroup m := (1, QuaternionGroup.a 1)

end Instances

end CFSG.GH74.E2
