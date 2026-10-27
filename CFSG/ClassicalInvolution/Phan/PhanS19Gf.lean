module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

instance fact_no_root_gf49 : Fact (∀ r : ZMod 7, r ^ 2 ≠ (-1 : ZMod 7) + 0 * r) :=
  ⟨by decide⟩

abbrev GF49 : Type := QuadraticAlgebra (ZMod 7) (-1) 0

structure V7 where
  x0 : GF49
  x1 : GF49
  x2 : GF49
  x3 : GF49
  x4 : GF49
  x5 : GF49
  x6 : GF49
  deriving DecidableEq

@[expose] def conj49 (x : GF49) : GF49 := star x

@[expose] def bfC (x y : V7) : GF49 :=
  x.x0 * y.x3 + y.x0 * x.x3 + (x.x1 * y.x4 + y.x1 * x.x4) + (x.x2 * y.x5 + y.x2 * x.x5) +
    (-2) * (x.x6 * y.x6)

@[expose] def tauC (x : V7) : V7 :=
  ⟨conj49 x.x3, conj49 x.x4, conj49 x.x5, conj49 x.x0, conj49 x.x1, conj49 x.x2, conj49 x.x6⟩

@[expose] def herC (x y : V7) : GF49 := bfC x (tauC y)

@[expose] def gramC (x y : V7) : GF49 := herC x x * herC y y - herC x y * herC y x

@[expose] def isFFC (x : V7) : Bool := bfC x x == 0 && herC x x != 0

@[expose] def colC (x y : V7) : Bool := bfC x y == 0 && gramC x y != 0

@[expose] def smulC (c : GF49) (x : V7) : V7 :=
  ⟨c * x.x0, c * x.x1, c * x.x2, c * x.x3, c * x.x4, c * x.x5, c * x.x6⟩

@[expose] def e0C : V7 := ⟨1, 0, 0, 0, 0, 0, 0⟩

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
