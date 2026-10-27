module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8MB

public section

namespace CFSG.ComponentClassification.HSFLit.Sec8

namespace MB

@[expose] def bit (x : MB) (i : ℕ) : Bool := (tget nfTabMB 8 (16 * x.g.val + x.a.val)).testBit i

@[expose] def ccount (x : MB) : ℕ := (Finset.univ.filter fun g : MB => g * x = x * g).card

@[expose] def inQC (x : MB) : Bool := !bit x 1 && (bit x 3 == bit x 6)

@[expose] def inMb (x : MB) : Bool := bit x 3 == bit x 6

@[expose] def ofPred (p : MB → Bool) (h1 : p 1 = true)
    (hmul : ∀ x, p x = true → ∀ y, p y = true → p (x * y) = true)
    (hinv : ∀ x, p x = true → p x⁻¹ = true) : Subgroup MB where
  carrier := {x | p x = true}
  mul_mem' {a b} ha hb := hmul a ha b hb
  one_mem' := h1
  inv_mem' {a} ha := hinv a ha

theorem card_ofPred (p : MB → Bool) (h1 : p 1 = true)
    (hmul : ∀ x, p x = true → ∀ y, p y = true → p (x * y) = true)
    (hinv : ∀ x, p x = true → p x⁻¹ = true) :
    Nat.card (ofPred p h1 hmul hinv) = (Finset.univ.filter fun x => p x = true).card := by
  rw [show Nat.card (ofPred p h1 hmul hinv) = Nat.card {x : MB // p x = true} from rfl,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

@[expose] def Mb : Subgroup MB := ofPred inMb (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

theorem card_Mb : Nat.card Mb = 128 := by
  rw [Mb, card_ofPred]; decide +kernel

theorem QC_span : ∀ x : MB, inQC x = true → InSpan [w₂, w₁, z, y, k, t * v] x := by
  decide +kernel

theorem cand_fact : ∀ x : MB, x * x = 1 → x ≠ 1 → inQC x = false → ccount x ≤ 32 →
    inMb x = false := by decide +kernel

end MB

end CFSG.ComponentClassification.HSFLit.Sec8
