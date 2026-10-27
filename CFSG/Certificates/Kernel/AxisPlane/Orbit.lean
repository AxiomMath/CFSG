module

public import Certificates.Data.CFSGNative.MonsterAxis.Cover
public import Mathlib.Logic.Relation
public import Aesop.BuiltinRules
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.KC.AxisPlane

@[expose] def orbitOf (m : ℕ) (f : ℕ → ℕ → ℕ) (s : ℕ) : Set ℕ :=
  {v | Relation.ReflTransGen (fun a b => ∃ g < m, b = f g a) s v}

@[expose] def natOrbit (rows : Array (Array ℕ)) (s : ℕ) : Set ℕ :=
  orbitOf rows.size (CFSG.Monster.AxisCount.Native.Cover.cvImg rows) s

end CFSG.KC.AxisPlane

end
