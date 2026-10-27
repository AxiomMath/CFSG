module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.SmallF3.Omega

structure Sec8T84Dec33 {E : Type} [Group E] (A1 A2 : Subgroup (MulAut E)) (E1 E2 : Subgroup E) :
    Prop where
  card1 : Nat.card E1 = 2 ^ 4
  card2 : Nat.card E2 = 2 ^ 4
  inf : E1 ⊓ E2 = ⊥
  sup : E1 ⊔ E2 = ⊤
  inv1 : ∀ a ∈ A1, ∀ x ∈ E1, a x ∈ E1
  inv2 : ∀ b ∈ A2, ∀ x ∈ E2, b x ∈ E2
  triv1 : ∀ a ∈ A1, ∀ x ∈ E2, a x = x
  triv2 : ∀ b ∈ A2, ∀ x ∈ E1, b x = x
  fix1 : ∀ x : E, (∀ a ∈ A1, a x = x) → x ∈ E2
  fix2 : ∀ x : E, (∀ b ∈ A2, b x = x) → x ∈ E1
  fpf1 : ∀ a ∈ A1, orderOf a = 5 → ∀ x ∈ E1, a x = x → x = 1
  fpf2 : ∀ b ∈ A2, orderOf b = 5 → ∀ x ∈ E2, b x = x → x = 1
  trans1 : ∀ v ∈ E1, v ≠ 1 → ∀ w ∈ E1, w ≠ 1 → ∃ a ∈ A1, a v = w
  trans2 : ∀ v ∈ E2, v ≠ 1 → ∀ w ∈ E2, w ≠ 1 → ∃ b ∈ A2, b v = w

end CFSG.OddStandard.SmallF3.Omega
