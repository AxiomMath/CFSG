module

public import Aesop.BuiltinRules
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.GH74.GLS.SP.Local

structure SPLCoord {F : Type*} [Field F] {P : Type*} [Group P] (x₁ x₂ x₃ x₄ : F → P) : Prop where
  add₁ : ∀ s s', x₁ (s + s') = x₁ s * x₁ s'
  add₂ : ∀ c c', x₂ (c + c') = x₂ c * x₂ c'
  add₃ : ∀ a a', x₃ (a + a') = x₃ a * x₃ a'
  add₄ : ∀ b b', x₄ (b + b') = x₄ b * x₄ b'
  surj : ∀ g : P, ∃ s c a b, g = x₁ s * x₂ c * x₃ a * x₄ b
  inj : ∀ s c a b s' c' a' b', x₁ s * x₂ c * x₃ a * x₄ b = x₁ s' * x₂ c' * x₃ a' * x₄ b' →
    s = s' ∧ c = c' ∧ a = a' ∧ b = b'
  cen₂ : ∀ c g, x₂ c * g = g * x₂ c
  c13 : ∀ s a, x₁ s * x₃ a = x₃ a * x₁ s
  c34 : ∀ a b, x₃ a * x₄ b = x₄ b * x₃ a * x₂ (a * b)
  c14 : ∀ s b, x₁ s * x₄ b = x₄ b * x₃ (s * b) * x₂ (s * b ^ 2 / 2) * x₁ s

end CFSG.GH74.GLS.SP.Local
