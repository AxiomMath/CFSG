module

public import Certificates.Data.Kernel.Spor.Fi24Base

public section

namespace CFSG.KS.Fi24Base

open CFSG.KC.Loop CFSG.KC.Fi24Base CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi24.Native
  Timmesfeld.Fi24Cl CFSG.HardMathSupport.Dickson.I271.RkBMFi24Inv
  CFSG.LocalAnalysis.GLTheoremA.S8.CfgI.Fi24Cfg

variable {L : Array Table} {f : Nat → Nat → Nat}

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem apF_cons (l : Nat) (w : List Nat) (x : Nat) :
    apF f (l :: w) x = letF f l (apF f w x) :=
  strictN_eq _ _

theorem letF_of_lt {l : Nat} (hl : l < 26) (x : Nat) : letF f l x = f l x := by
  have h : Nat.blt l 26 = true := by
    rw [Nat.blt_eq]
    exact hl
  unfold letF
  rw [h]

theorem letF_of_ge {l : Nat} (hl : 26 ≤ l) (x : Nat) : letF f l x = 0 := by
  have h : Nat.blt l 26 = false := by
    cases h' : Nat.blt l 26
    · rfl
    · rw [Nat.blt_eq] at h'
      omega
  unfold letF
  rw [h]

theorem ap_letF (hS : L.size = 26) (hL : ∀ l < 26, ∀ x < 306936, ap L[l]! x = f l x) :
    ∀ l x, x < 306936 → ap L[l]! x = letF f l x := by
  intro l x hx
  by_cases hl : l < 26
  · rw [letF_of_lt hl]
    exact hL l hl x hx
  · rw [letF_of_ge (by omega), getElem!_neg L l (by omega)]
    rfl

theorem letF_lt (hlt : ∀ l < 26, ∀ x < 306936, f l x < 306936) :
    ∀ l x, x < 306936 → letF f l x < 306936 := by
  intro l x hx
  by_cases hl : l < 26
  · rw [letF_of_lt hl]
    exact hlt l hl x hx
  · rw [letF_of_ge (by omega)]
    omega

theorem apWord_eq (hL : ∀ l x, x < 306936 → ap L[l]! x = letF f l x)
    (hlt : ∀ l x, x < 306936 → letF f l x < 306936) :
    ∀ w x, x < 306936 → apWord L w x = apF f w x ∧ apF f w x < 306936
  | [], x, hx => ⟨rfl, hx⟩
  | l :: w, x, hx => by
    obtain ⟨e, h⟩ := apWord_eq hL hlt w x hx
    have e2 : apWord L (l :: w) x = ap L[l]! (apWord L w x) := rfl
    rw [e2, apF_cons, e, hL l _ h]
    exact ⟨rfl, hlt l _ h⟩

theorem beq_eq_nbeq (a b : Nat) : (a == b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · simp only [beq_eq_false_iff_ne]
    intro e
    rw [e, Nat.beq_refl] at h
    exact Bool.noConfusion h
  · simp only [beq_iff_eq]
    exact Nat.eq_of_beq_eq_true h

theorem eqL_eq (u v : List Nat) : ∀ B : List Nat,
    eqL f u v B = B.all fun b => apF f u b == apF f v b
  | [] => rfl
  | b :: B => by
    rw [List.all_cons, ← eqL_eq u v B, beq_eq_nbeq]
    change Bool.rec (motive := fun _ => Bool) false (eqL f u v B)
      (Nat.beq (apF f u b) (apF f v b)) = _
    cases Nat.beq (apF f u b) (apF f v b) <;> rfl

theorem eqOnBase_eq (hL : ∀ l x, x < 306936 → ap L[l]! x = letF f l x)
    (hlt : ∀ l x, x < 306936 → letF f l x < 306936) (u v : List Nat) :
    eqOnBase L u v = eqB f u v := by
  have hw : ∀ w b, b < 306936 → apWord L w b = apF f w b := fun w b hb =>
    (apWord_eq hL hlt w b hb).1
  have hB : chainBase.toList = [0, 305530, 5604, 221549, 266275, 186844] := rfl
  unfold eqOnBase eqB
  rw [eqL_eq, ← Array.all_toList, hB]
  simp only [List.all_cons, List.all_nil, hw u 0 (by omega), hw v 0 (by omega),
    hw u 305530 (by omega), hw v 305530 (by omega), hw u 5604 (by omega), hw v 5604 (by omega),
    hw u 221549 (by omega), hw v 221549 (by omega), hw u 266275 (by omega),
    hw v 266275 (by omega), hw u 186844 (by omega), hw v 186844 (by omega)]

theorem eqOnBase_fun {O : Enum} (hS : (chainLetters O).size = 26)
    (hL : ∀ l < 26, ∀ x < 306936, ap (chainLetters O)[l]! x = f l x)
    (hlt : ∀ l < 26, ∀ x < 306936, f l x < 306936) :
    eqOnBase (chainLetters O) = eqB f :=
  funext fun u => funext fun v => eqOnBase_eq (ap_letF hS hL) (letF_lt hlt) u v

theorem cfgCheck_eq {O : Enum} (hS : (chainLetters O).size = 26)
    (hL : ∀ l < 26, ∀ x < 306936, ap (chainLetters O)[l]! x = f l x)
    (hlt : ∀ l < 26, ∀ x < 306936, f l x < 306936) :
    cfgCheck O = cfgG (eqB f) := by
  rw [← eqOnBase_fun hS hL hlt]
  rfl

theorem invCheck_eq {O : Enum} (hS : (chainLetters O).size = 26)
    (hL : ∀ l < 26, ∀ x < 306936, ap (chainLetters O)[l]! x = f l x)
    (hlt : ∀ l < 26, ∀ x < 306936, f l x < 306936) :
    invCheck O = invG (eqB f) := by
  rw [← eqOnBase_fun hS hL hlt]
  rfl

end CFSG.KS.Fi24Base

end
