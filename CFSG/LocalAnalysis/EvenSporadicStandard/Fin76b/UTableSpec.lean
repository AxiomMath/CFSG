module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.EvenSporadicStandard.Fin76b

@[expose] def dMul (i j : ℕ) : ℕ :=
  if i < 4 then
    (if j < 4 then (i + j) % 4 else 4 + ((j - 4) + 4 - i) % 4)
  else
    (if j < 4 then 4 + ((i - 4) + j) % 4 else ((j - 4) + 4 - (i - 4)) % 4)

@[expose] def UPeq (mulE : ℕ → ℕ → ℕ) (tI : ℕ) (x y : ℕ × ℕ) : Prop :=
  x = y ∨ y = (dMul x.1 2, mulE x.2 tI)

structure UWitness (mulE : ℕ → ℕ → ℕ) (tI : ℕ) (u : ℕ × ℕ) (φ : ℕ → ℕ × ℕ) : Prop where
  range : ∀ a < 32, (φ a).1 < 8 ∧ (φ a).2 < 32
  mul : ∀ a < 32, ∀ b < 32,
    UPeq mulE tI (φ (mulE a b)) (dMul (φ a).1 (φ b).1, mulE (φ a).2 (φ b).2)
  inj : ∀ a < 32, ∀ b < 32, UPeq mulE tI (φ a) (φ b) → a = b
  comm : ∀ a < 32, UPeq mulE tI (dMul (φ a).1 u.1, mulE (φ a).2 u.2)
    (dMul u.1 (φ a).1, mulE u.2 (φ a).2)
  ne : ∀ a < 32, ¬ UPeq mulE tI (φ a) u

structure UTableSpec (mulE : ℕ → ℕ → ℕ) (tI : ℕ) : Prop where
  tI_lt : tI < 32
  tI_ne : tI ≠ 0
  tI_sq : mulE tI tI = 0
  center : ∀ a < 32, (∀ b < 32, mulE a b = mulE b a) → a = 0 ∨ a = tI
  wit : ∀ i < 8, ∀ k < 32, UPeq mulE tI (dMul i i, mulE k k) (0, 0) →
    ¬ UPeq mulE tI (i, k) (0, 0) → ¬ UPeq mulE tI (i, k) (0, tI) →
    ∃ φ, UWitness mulE tI (i, k) φ

end CFSG.EvenSporadicStandard.Fin76b
