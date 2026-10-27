module

public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.ComponentClassification.AS76b.Sec5

@[expose] def E (β : Bool) (M : ℕ) (g : Bool → Bool → ℕ) : ℕ :=
  if β then g false true + g true false + M * g true true
  else g false false + (M + 1) * g true true

@[expose] def cform (χ : Bool × Bool × Bool → ℕ) (π : Bool × Bool × Bool) (M Q : ℕ) : ℕ :=
  E π.1 M fun σ₁ τ₁ => E π.2.1 Q fun σ₂ τ₂ => E π.2.2 Q fun σ₃ τ₃ =>
    χ (σ₁, σ₂, σ₃) * χ (τ₁, τ₂, τ₃)

@[expose] def chi6 (eU eW eiU eiW es et : Bool) : Bool × Bool × Bool → ℕ
  | (false, false, false) => 0
  | (true, false, false) => 1
  | (false, true, false) => if eU then 1 else 0
  | (false, false, true) => if eW then 1 else 0
  | (true, true, false) => if eiU then 1 else 0
  | (true, false, true) => if eiW then 1 else 0
  | (false, true, true) => if es then 1 else 0
  | (true, true, true) => if et then 1 else 0

theorem arith (eU eW eiU eiW es et : Bool) (k l : ℕ) (hlk : l ≤ k)
    (hU : eU = true → eiU = false) (hW : eW = true → eiW = false) (h3 : es = true ∨ et = true)
    (hqU : eU = true → k = l) (hqW : eW = true → k = l)
    (hc : ∀ p, chi6 eU eW eiU eiW es et p = 1 →
      cform (chi6 eU eW eiU eiW es et) p (4 * l + 2) (4 * k + 2) =
        cform (chi6 eU eW eiU eiW es et) (true, false, false) (4 * l + 2) (4 * k + 2)) :
    (eU = false ∧ eW = false ∧ eiU = true ∧ eiW = true ∧ es = false ∧ et = true) ∨
    (eU = true ∧ eW = true ∧ es = false ∧ et = true ∧ l = 0) ∨
    (eU = true ∧ eW = false ∧ eiW = true ∧ es = true ∧ et = false) ∨
    (eU = false ∧ eW = true ∧ eiU = true ∧ es = true ∧ et = false) := by
  have c1 := hc (false, true, false)
  have c2 := hc (false, false, true)
  have c3 := hc (true, true, false)
  have c4 := hc (true, false, true)
  have c5 := hc (false, true, true)
  have c6 := hc (true, true, true)
  clear hc
  cases eU <;> cases eW <;> cases eiU <;> cases eiW <;> cases es <;> cases et <;>
    simp only [chi6, cform, E, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, mul_one,
      mul_zero, add_zero, zero_add, forall_const, imp_false, false_or, or_false, or_true,
      and_true, true_and, and_false, false_and, not_false_eq_true, IsEmpty.forall_iff,
      zero_ne_one] at hU hW h3 hqU hqW c1 c2 c3 c4 c5 c6 ⊢ <;>
    (try subst hqU) <;> (try subst hqW) <;> (try ring_nf at c1) <;> (try ring_nf at c2) <;>
    (try ring_nf at c3) <;> (try ring_nf at c4) <;> (try ring_nf at c5) <;>
    (try ring_nf at c6) <;> omega

end CFSG.ComponentClassification.AS76b.Sec5
