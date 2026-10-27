module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.KC.LQT.Syl.CoreSnd

variable {G : Type*} [Group G]

@[expose] def elt (k : ℕ) (B : List G) (m : ℕ) : G :=
  (List.range k).foldl (fun acc i => if m.testBit i then acc * B.getD i 1 else acc) 1

@[expose] def lst (B : List G) : List G := (List.range 16).map (elt 4 B)

structure EFacts (B : List G) : Prop where
  len : B.length = 4
  nodup : (lst B).Nodup
  sq : ∀ b ∈ B, b * b = 1
  comm : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b

@[expose] def Cm (B : List G) (σ : G) (u : ℕ) : Prop :=
  σ * elt 4 B u = elt 4 B u * σ

instance [DecidableEq G] (B : List G) (σ : G) : DecidablePred (Cm B σ) := fun u =>
  inferInstanceAs (Decidable (σ * elt 4 B u = elt 4 B u * σ))

end CFSG.KC.LQT.Syl.CoreSnd

end
