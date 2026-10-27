module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.GF2Type.Smith1979.GammaU

abbrev V12 : Type := Fin 12 → ZMod 2

abbrev lo (i : Fin 6) : Fin 12 := Fin.castAdd 6 i

abbrev hi (i : Fin 6) : Fin 12 := Fin.natAdd 6 i

@[expose] def q0 (x : V12) : ZMod 2 := ∑ i : Fin 6, (x (lo i) + x (lo i) * x (hi i) + x (hi i))

theorem ext_lo_hi {x y : V12} (h₁ : ∀ i, x (lo i) = y (lo i)) (h₂ : ∀ i, x (hi i) = y (hi i)) :
    x = y :=
  funext fun j => Fin.addCases (m := 6) (n := 6) h₁ h₂ j

@[expose] def theta0Fun (x : V12) : V12 :=
  Fin.append (fun i => x (hi i)) (fun i => x (lo i) + x (hi i))

theorem theta0Fun_lo (x : V12) (i : Fin 6) : theta0Fun x (lo i) = x (hi i) :=
  Fin.append_left _ _ i

theorem theta0Fun_hi (x : V12) (i : Fin 6) : theta0Fun x (hi i) = x (lo i) + x (hi i) :=
  Fin.append_right _ _ i

@[expose] def theta0 : V12 →ₗ[ZMod 2] V12 where
  toFun := theta0Fun
  map_add' x y := ext_lo_hi (fun i => by simp only [theta0Fun_lo, Pi.add_apply])
    (fun i => by simp only [theta0Fun_hi, Pi.add_apply]; abel)
  map_smul' c x := ext_lo_hi (fun i => by simp [theta0Fun_lo])
    (fun i => by simp only [theta0Fun_hi, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)

@[simp] theorem theta0_lo (x : V12) (i : Fin 6) : theta0 x (lo i) = x (hi i) :=
  theta0Fun_lo x i

@[simp] theorem theta0_hi (x : V12) (i : Fin 6) : theta0 x (hi i) = x (lo i) + x (hi i) :=
  theta0Fun_hi x i

end CFSG.GF2Type.Smith1979.GammaU
