module

public import CFSG.GH74.E2.AutCert
public import CFSG.CharacterTheory.Semidihedral.NormalForm
public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public meta import CFSG.Open.Catalog

public section

namespace CFSG.GH74.E2

open CFSG.Semidihedral
abbrev SD16M : Type := Model 4 (by norm_num)

section Relations

variable {M : Type*} [Group M]

@[expose] def RelA (a b : M) : Prop :=
  a ^ 8 = 1 ∧ b ^ 2 = 1 ∧ b * a * b⁻¹ = a ^ 3 ∧ a ^ 4 ≠ 1 ∧ b ≠ 1

@[expose] def RelB (m : ℕ) (a b c : M) : Prop :=
  c ^ (2 * m) = 1 ∧ c * a = a * c ∧ c * b = b * c ∧ c ^ m ≠ 1

@[expose] def RelC (m : ℕ) (a b c d : M) : Prop :=
  d ^ 2 = c ^ m ∧ d * c * d⁻¹ = c⁻¹ ∧ d * a = a * d ∧ d * b = b * d

end Relations

section Certificate

variable (m : ℕ)

@[expose] def CentralPow (c : SD16M × QuaternionGroup m) : Prop :=
  ∀ y : SD16M × QuaternionGroup m, y * c ^ m = c ^ m * y

@[expose] def Search4 (a b c : SD16M × QuaternionGroup m) : Prop :=
  ∀ d : SD16M × QuaternionGroup m, RelC m a b c d → False

@[expose] def Search3 (t₀ : SD16M × QuaternionGroup m) (a b : SD16M × QuaternionGroup m) : Prop :=
  ∀ c : SD16M × QuaternionGroup m, RelB m a b c → CentralPow m c → c ^ m ≠ t₀ → Search4 m a b c

@[expose] def Search2 (t₀ : SD16M × QuaternionGroup m) (a : SD16M × QuaternionGroup m) : Prop :=
  ∀ b : SD16M × QuaternionGroup m, RelA a b → Search3 m t₀ a b

@[expose] def SearchOK (t₀ : SD16M × QuaternionGroup m) : Prop :=
  ∀ a : SD16M × QuaternionGroup m, a ^ 8 = 1 → Search2 m t₀ a

section Decidability

variable [NeZero m]

end Decidability

end Certificate

section Instances

@[expose] def gx (m : ℕ) [NeZero m] : SD16M × QuaternionGroup m := (modelR 4 (by norm_num), 1)

@[expose] def gy (m : ℕ) [NeZero m] : SD16M × QuaternionGroup m := (modelS 4 (by norm_num), 1)

@[expose] def gc (m : ℕ) [NeZero m] : SD16M × QuaternionGroup m := (1, QuaternionGroup.a 1)

@[expose] def gd (m : ℕ) [NeZero m] : SD16M × QuaternionGroup m := (1, QuaternionGroup.xa 0)

end Instances

end CFSG.GH74.E2
