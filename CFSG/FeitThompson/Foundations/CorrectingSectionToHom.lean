module

public import CFSG.FeitThompson.Foundations.QuotientActsOnAbelianNormal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped IsMulCommutative

variable {G : Type*} [Group G] {A : Subgroup G} [A.Normal] [IsMulCommutative ↥A]

omit [A.Normal] [IsMulCommutative ↥A] in
theorem coe_toMul_add (a c : Additive ↥A) :
    (((a + c).toMul : ↥A) : G) = ((a.toMul : ↥A) : G) * ((c.toMul : ↥A) : G) := (rfl)

omit [A.Normal] [IsMulCommutative ↥A] in
theorem coe_toMul_zero : (((0 : Additive ↥A).toMul : ↥A) : G) = 1 := (rfl)

theorem coe_toMul_smul_of_section {s : G ⧸ A → G} (hs : ∀ x, ((s x : G) : G ⧸ A) = x)
    (x : G ⧸ A) (a : Additive ↥A) :
    (((x • a).toMul : ↥A) : G) = s x * ((a.toMul : ↥A) : G) * (s x)⁻¹ := by
  have h := coe_toMul_quotientMk_smul A (s x) a
  rw [hs] at h
  exact h

def correctedSection (s : G ⧸ A → G) (b : G ⧸ A → Additive ↥A) (x : G ⧸ A) : G :=
  (((-b x).toMul : ↥A) : G) * s x

omit [A.Normal] [IsMulCommutative ↥A] in
theorem correctedSection_apply (s : G ⧸ A → G) (b : G ⧸ A → Additive ↥A) (x : G ⧸ A) :
    correctedSection s b x = (((-b x).toMul : ↥A) : G) * s x := (rfl)

omit [IsMulCommutative ↥A] in
@[simp] theorem mk_correctedSection {s : G ⧸ A → G} (hs : ∀ x, ((s x : G) : G ⧸ A) = x)
    (b : G ⧸ A → Additive ↥A) (x : G ⧸ A) :
    ((correctedSection s b x : G) : G ⧸ A) = x := by
  rw [correctedSection_apply, QuotientGroup.mk_mul, hs,
    (QuotientGroup.eq_one_iff _).2 (((-b x).toMul : ↥A)).2, one_mul]

theorem correctedSection_one_of_normalized {s : G ⧸ A → G} (hs1 : s 1 = 1)
    {b : G ⧸ A → Additive ↥A} (hb1 : b 1 = 0) : correctedSection s b 1 = 1 := by
  rw [correctedSection_apply, hs1, hb1, neg_zero, coe_toMul_zero, mul_one]

theorem correctedSection_mul {s : G ⧸ A → G} (hs : ∀ x, ((s x : G) : G ⧸ A) = x)
    {b : G ⧸ A → Additive ↥A}
    (hb : ∀ x y, s x * s y * (s (x * y))⁻¹ = (((b x + x • b y - b (x * y)).toMul : ↥A) : G))
    (x y : G ⧸ A) :
    correctedSection s b x * correctedSection s b y = correctedSection s b (x * y) := by
  have key : s x * s y = (((b x + x • b y - b (x * y)).toMul : ↥A) : G) * s (x * y) := by
    rw [← hb]; group
  have step : s x * (((-b y).toMul : ↥A) : G) = (((x • (-b y)).toMul : ↥A) : G) * s x := by
    rw [coe_toMul_smul_of_section hs]; group
  have add_key : (-b x) + x • (-b y) + (b x + x • b y - b (x * y)) = -b (x * y) := by
    rw [smul_neg]; abel
  simp only [correctedSection_apply]
  calc (((-b x).toMul : ↥A) : G) * s x * ((((-b y).toMul : ↥A) : G) * s y)
      = (((-b x).toMul : ↥A) : G) * ((s x * (((-b y).toMul : ↥A) : G)) * s y) := by group
    _ = (((-b x).toMul : ↥A) : G) * (((((x • (-b y)).toMul : ↥A) : G) * s x) * s y) := by
        rw [step]
    _ = ((((-b x) + x • (-b y)).toMul : ↥A) : G) * (s x * s y) := by
        rw [coe_toMul_add]; group
    _ = ((((-b x) + x • (-b y)).toMul : ↥A) : G) *
          ((((b x + x • b y - b (x * y)).toMul : ↥A) : G) * s (x * y)) := by rw [key]
    _ = ((((-b x) + x • (-b y) + (b x + x • b y - b (x * y))).toMul : ↥A) : G) * s (x * y) := by
        simp only [coe_toMul_add]; group
    _ = (((-b (x * y)).toMul : ↥A) : G) * s (x * y) := by rw [add_key]

def correctedSectionHom {s : G ⧸ A → G} (hs : ∀ x, ((s x : G) : G ⧸ A) = x)
    {b : G ⧸ A → Additive ↥A}
    (hb : ∀ x y, s x * s y * (s (x * y))⁻¹ = (((b x + x • b y - b (x * y)).toMul : ↥A) : G)) :
    (G ⧸ A) →* G :=
  MonoidHom.mk' (correctedSection s b) fun x y => (correctedSection_mul hs hb x y).symm

@[simp] theorem correctedSectionHom_apply {s : G ⧸ A → G} (hs : ∀ x, ((s x : G) : G ⧸ A) = x)
    {b : G ⧸ A → Additive ↥A}
    (hb : ∀ x y, s x * s y * (s (x * y))⁻¹ = (((b x + x • b y - b (x * y)).toMul : ↥A) : G))
    (x : G ⧸ A) :
    correctedSectionHom hs hb x = (((-b x).toMul : ↥A) : G) * s x := (rfl)

@[simp]
theorem mk_correctedSectionHom {s : G ⧸ A → G} (hs : ∀ x, ((s x : G) : G ⧸ A) = x)
    {b : G ⧸ A → Additive ↥A}
    (hb : ∀ x y, s x * s y * (s (x * y))⁻¹ = (((b x + x • b y - b (x * y)).toMul : ↥A) : G))
    (x : G ⧸ A) :
    ((correctedSectionHom hs hb x : G) : G ⧸ A) = x := by
  rw [correctedSectionHom_apply, ← correctedSection_apply, mk_correctedSection hs]

end CFSG.FeitThompson
