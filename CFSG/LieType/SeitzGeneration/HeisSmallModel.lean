module

public import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LieType.SeitzGeneration.HeisSmall

class NoCubeRoot (F : Type) [Field F] : Prop where
  ne_zero : ∀ x : F, x * x + x + 1 ≠ 0

@[ext] structure QExt (F : Type) where
  re : F
  im : F
deriving DecidableEq

namespace QExt

variable {F : Type} [Field F]

instance : Zero (QExt F) := ⟨⟨0, 0⟩⟩

instance : One (QExt F) := ⟨⟨1, 0⟩⟩

instance : Add (QExt F) := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩

instance : Neg (QExt F) := ⟨fun x => ⟨-x.re, -x.im⟩⟩

instance : Mul (QExt F) :=
  ⟨fun x y => ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re - x.im * y.im⟩⟩

@[expose] def norm (x : QExt F) : F := x.re * x.re - x.re * x.im + x.im * x.im

instance : Inv (QExt F) := ⟨fun x => ⟨(norm x)⁻¹ * (x.re - x.im), -((norm x)⁻¹ * x.im)⟩⟩

@[simp] theorem zero_re : (0 : QExt F).re = 0 := rfl
@[simp] theorem zero_im : (0 : QExt F).im = 0 := rfl
@[simp] theorem one_re : (1 : QExt F).re = 1 := rfl
@[simp] theorem one_im : (1 : QExt F).im = 0 := rfl
@[simp] theorem add_re (x y : QExt F) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : QExt F) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : QExt F) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : QExt F) : (-x).im = -x.im := rfl
@[simp] theorem mul_re (x y : QExt F) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] theorem mul_im (x y : QExt F) :
    (x * y).im = x.re * y.im + x.im * y.re - x.im * y.im := rfl
@[simp] theorem inv_re (x : QExt F) : x⁻¹.re = (norm x)⁻¹ * (x.re - x.im) := rfl
@[simp] theorem inv_im (x : QExt F) : x⁻¹.im = -((norm x)⁻¹ * x.im) := rfl

theorem norm_ne_zero [NoCubeRoot F] {x : QExt F} (hx : x ≠ 0) : norm x ≠ 0 := by
  intro h
  by_cases hb : x.im = 0
  · have h1 : x.re * x.re = 0 := by simpa [norm, hb] using h
    exact hx (QExt.ext (mul_self_eq_zero.1 h1) hb)
  · refine NoCubeRoot.ne_zero (-(x.re / x.im)) ?_
    have h2 : x.re * x.re - x.re * x.im + x.im * x.im = 0 := h
    field_simp
    linear_combination h2

instance [NoCubeRoot F] : Field (QExt F) :=
  Field.ofMinimalAxioms (QExt F)
    (fun a b c => by ext <;> simp <;> ring)
    (fun a => by ext <;> simp)
    (fun a => by ext <;> simp)
    (fun a b c => by ext <;> simp <;> ring)
    (fun a b => by ext <;> simp <;> ring)
    (fun a => by ext <;> simp)
    (fun a ha => by
      have h := norm_ne_zero ha
      ext
      · simp only [mul_re, inv_re, inv_im, one_re]
        rw [show a.re * ((norm a)⁻¹ * (a.re - a.im)) - a.im * -((norm a)⁻¹ * a.im) =
          (norm a)⁻¹ * (a.re * a.re - a.re * a.im + a.im * a.im) by ring]
        exact inv_mul_cancel₀ h
      · simp only [mul_im, inv_re, inv_im, one_im]
        ring)
    (by ext <;> simp [norm])
    (fun a b c => by ext <;> simp <;> ring)
    ⟨0, 1, fun h => zero_ne_one (congrArg QExt.re h)⟩

omit [Field F] in
instance [Fintype F] : Fintype (QExt F) :=
  Fintype.ofEquiv (F × F) ⟨fun p => ⟨p.1, p.2⟩, fun x => (x.re, x.im), fun _ => rfl, fun _ => rfl⟩

omit [Field F] in
theorem card_eq [Fintype F] : Fintype.card (QExt F) = Fintype.card F ^ 2 := by
  rw [Fintype.card_congr (show QExt F ≃ F × F from
    ⟨fun x => (x.re, x.im), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩), Fintype.card_prod,
    sq]

@[expose] def omega : QExt F := ⟨0, 1⟩

theorem omega_pow_three [NoCubeRoot F] : (omega : QExt F) ^ 3 = 1 := by
  ext <;> simp [pow_succ, omega]

theorem omega_ne_one [NoCubeRoot F] : (omega : QExt F) ≠ 1 := fun h =>
  zero_ne_one (congrArg QExt.im h : (1 : F) = 0).symm

end QExt

structure GF8 where
  val : Fin 8
deriving DecidableEq

namespace GF8

@[expose] def ofNat' (n : ℕ) : GF8 := ⟨⟨n % 8, Nat.mod_lt n (by norm_num)⟩⟩

@[expose] def toNat (a : GF8) : ℕ := a.val.val

@[expose] def mulNat (a b : ℕ) : ℕ :=
  let r := (if b &&& 1 = 1 then a else 0) ^^^ (if b &&& 2 = 2 then a <<< 1 else 0) ^^^
    (if b &&& 4 = 4 then a <<< 2 else 0)
  let r := if r &&& 16 = 16 then r ^^^ 22 else r
  if r &&& 8 = 8 then r ^^^ 11 else r

instance : Zero GF8 := ⟨ofNat' 0⟩

instance : One GF8 := ⟨ofNat' 1⟩

instance : Add GF8 := ⟨fun a b => ofNat' (a.toNat ^^^ b.toNat)⟩

instance : Neg GF8 := ⟨fun a => a⟩

instance : Mul GF8 := ⟨fun a b => ofNat' (mulNat a.toNat b.toNat)⟩

instance : Inv GF8 :=
  ⟨fun a => ofNat' (mulNat (mulNat a.toNat a.toNat) (mulNat (mulNat a.toNat a.toNat)
    (mulNat a.toNat a.toNat)))⟩

instance : Fintype GF8 :=
  Fintype.ofEquiv (Fin 8) ⟨GF8.mk, GF8.val, fun _ => rfl, fun _ => rfl⟩

instance : Field GF8 :=
  Field.ofMinimalAxioms GF8 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem card_eq : Fintype.card GF8 = 8 := rfl

end GF8

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

instance : Fact (Nat.Prime 11) := ⟨by decide⟩

instance : NoCubeRoot (ZMod 5) := ⟨by decide⟩

instance : NoCubeRoot (ZMod 11) := ⟨by decide⟩

instance : NoCubeRoot GF8 := ⟨by decide⟩

abbrev Q5 : Type := QExt (ZMod 5)

abbrev Q8 : Type := QExt GF8

abbrev Q11 : Type := QExt (ZMod 11)

theorem card_q5 : Fintype.card Q5 = 5 ^ 2 := by
  rw [QExt.card_eq, ZMod.card]

theorem card_q8 : Fintype.card Q8 = 8 ^ 2 := by
  rw [QExt.card_eq, GF8.card_eq]

theorem card_q11 : Fintype.card Q11 = 11 ^ 2 := by
  rw [QExt.card_eq, ZMod.card]

end CFSG.LieType.SeitzGeneration.HeisSmall
