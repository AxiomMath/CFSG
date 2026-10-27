module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Finset.Defs

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

variable {n : ℕ}

structure BlockData (M : Subgroup (Equiv.Perm (Fin n))) (m t : ℕ) where
  gens : List ↥M
  B₀ : Finset (Fin n)
  H : List (Finset (Fin n))
  hp : List ℕ
  hl : List ℕ
  ks : List ↥M
  Es : List ↥M
  r₁ : Finset (Fin n)
  R₁ : List (Finset (Fin n))
  p₁ : List ℕ
  l₁ : List ℕ
  r₂ : Finset (Fin n)
  R₂ : List (Finset (Fin n))
  p₂ : List ℕ
  l₂ : List ℕ
  c₁ : ℕ
  c₂ : ℕ
  t₀ : Fin t → Fin n
  T : List (Fin t → Fin n)
  tp : List ℕ
  tl : List ℕ
  e : ℕ
  u : ℕ
  u' : ℕ

end CFSG.QuasithinUnique.Vol2Native.L239
