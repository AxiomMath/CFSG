module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.SetTheory.Cardinal.Finite

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {Q : Type*} {M : Type*}

def cocycleProd [Fintype Q] [CommMonoid M] (α : Q → Q → M) (x : Q) : M := ∏ z, α x z

theorem cocycleProd_apply [Fintype Q] [CommMonoid M] (α : Q → Q → M) (x : Q) :
    cocycleProd α x = ∏ z, α x z := (rfl)

theorem cocycleProd_one [Fintype Q] [One Q] [CommMonoid M] {α : Q → Q → M}
    (h : ∀ z, α 1 z = 1) : cocycleProd α 1 = 1 := by
  simp [cocycleProd_apply, h]

theorem cocycleProd_ne_zero {K : Type*} [Fintype Q] [CommMonoidWithZero K] [NoZeroDivisors K]
    [Nontrivial K] {α : Q → Q → K} (h : ∀ x y, α x y ≠ 0) (x : Q) : cocycleProd α x ≠ 0 := by
  rw [cocycleProd_apply]
  exact Finset.prod_ne_zero_iff.2 fun z _ => h _ _

theorem pow_natCard_mul_cocycleProd [Group Q] [Fintype Q] [CommMonoid M] {α : Q → Q → M}
    (h : ∀ x y z, α x y * α (x * y) z = α x (y * z) * α y z) (x y : Q) :
    α x y ^ Nat.card Q * cocycleProd α (x * y) = cocycleProd α x * cocycleProd α y := by
  calc α x y ^ Nat.card Q * cocycleProd α (x * y)
      = ∏ z : Q, α x y * α (x * y) z := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          Nat.card_eq_fintype_card, cocycleProd_apply]
    _ = ∏ z : Q, α x (y * z) * α y z := Finset.prod_congr rfl fun z _ => h x y z
    _ = cocycleProd α x * cocycleProd α y := by
        rw [Finset.prod_mul_distrib, cocycleProd_apply, cocycleProd_apply]
        congr 1
        exact Equiv.prod_comp (Equiv.mulLeft y) (α x)

theorem pow_natCard_eq_cocycleProd_div {N : Type*} [Group Q] [Fintype Q] [CommGroup N]
    {α : Q → Q → N} (h : ∀ x y z, α x y * α (x * y) z = α x (y * z) * α y z) (x y : Q) :
    α x y ^ Nat.card Q = cocycleProd α x * cocycleProd α y / cocycleProd α (x * y) := by
  rw [eq_div_iff_mul_eq']
  exact pow_natCard_mul_cocycleProd h x y

theorem pow_natCard_eq_cocycleProd_div₀ {K : Type*} [Group Q] [Fintype Q] [Field K]
    {α : Q → Q → K} (h0 : ∀ x y, α x y ≠ 0)
    (h : ∀ x y z, α x y * α (x * y) z = α x (y * z) * α y z) (x y : Q) :
    α x y ^ Nat.card Q = cocycleProd α x * cocycleProd α y / cocycleProd α (x * y) := by
  rw [eq_div_iff_mul_eq (cocycleProd_ne_zero h0 _)]
  exact pow_natCard_mul_cocycleProd h x y

end CFSG.FeitThompson
