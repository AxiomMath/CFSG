module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59BLinTab
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

public section

namespace CFSG.OddStandard.SmallF3.FritzII.FzL59BLin

abbrev Q : Type := QuaternionGroup 2

abbrev N : Type := Q × Q × Q

abbrev X : Type := N × Bool × Bool

@[expose] def chiQ : Q → Bool
  | QuaternionGroup.a j => j.val % 2 == 1
  | QuaternionGroup.xa j => j.val % 2 == 1

@[expose] def psiQf : Q → Q
  | QuaternionGroup.a j =>
      match j.val with
      | 0 => QuaternionGroup.a 0
      | 1 => QuaternionGroup.xa 3
      | 2 => QuaternionGroup.a 2
      | _ => QuaternionGroup.xa 1
  | QuaternionGroup.xa j =>
      match j.val with
      | 0 => QuaternionGroup.xa 2
      | 1 => QuaternionGroup.a 3
      | 2 => QuaternionGroup.xa 0
      | _ => QuaternionGroup.a 1

theorem psiQf_mul : ∀ x y : Q, psiQf (x * y) = psiQf x * psiQf y := by decide

@[expose] def psiQ : Q →* Q where
  toFun := psiQf
  map_one' := rfl
  map_mul' := psiQf_mul

@[expose] def zp (b : Bool) : Q := if b then QuaternionGroup.a 2 else 1

@[expose] def xiN : N →* N where
  toFun n := (n.2.1, n.1, n.2.2)
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def psiNf (ε : Bool) (n : N) : N :=
  (psiQ n.1 * zp (ε && chiQ n.2.1), psiQ n.2.1 * zp (ε && chiQ n.2.2),
    psiQ n.2.2 * zp (ε && chiQ n.1))

theorem psiNf_mul (ε : Bool) (n m : N) : psiNf ε (n * m) = psiNf ε n * psiNf ε m := by
  have h : ∀ (ε : Bool) (x y u v : Q), psiQ (x * y) * zp (ε && chiQ (u * v))
      = (psiQ x * zp (ε && chiQ u)) * (psiQ y * zp (ε && chiQ v)) := by decide
  obtain ⟨n0, n1, n2⟩ := n
  obtain ⟨m0, m1, m2⟩ := m
  exact Prod.ext (h ε n0 m0 n1 m1) (Prod.ext (h ε n1 m1 n2 m2) (h ε n2 m2 n0 m0))

@[expose] def psiN (ε : Bool) : N →* N where
  toFun := psiNf ε
  map_one' := by decide +revert
  map_mul' := psiNf_mul ε

@[expose] def cN (ε : Bool) : N :=
  if ε then (QuaternionGroup.xa 0, QuaternionGroup.xa 0, QuaternionGroup.xa 0) else 1

@[expose] def zetaN : N := (QuaternionGroup.a 2, QuaternionGroup.a 2, QuaternionGroup.a 2)

@[expose] def twE (e : Bool) (n : N) : N := if e then xiN n else n

@[expose] def twF (ε f : Bool) (n : N) : N := if f then psiN ε n else n

@[expose] def star (ε : Bool) (x y : X) : X :=
  (x.1 * twE x.2.1 (twF ε x.2.2 y.1) * (if x.2.2 && y.2.1 then twE x.2.1 (cN ε)⁻¹ else 1),
    x.2.1 ^^ y.2.1, x.2.2 ^^ y.2.2)

@[expose] def oneX : X := (1, false, false)

@[expose] def ktr (x : X) : X := (x.1 * zetaN, x.2)

@[expose] def KEq (x y : X) : Prop := x = y ∨ x = ktr y

instance (x y : X) : Decidable (KEq x y) := by unfold KEq; infer_instance

@[expose] def IsInv (ε : Bool) (x : X) : Prop := ¬ KEq x oneX ∧ KEq (star ε x x) oneX

instance (ε : Bool) (x : X) : Decidable (IsInv ε x) := by unfold IsInv; infer_instance

@[expose] def decQ (v : Nat) : Q :=
  match v with
  | 0 => QuaternionGroup.a 0
  | 1 => QuaternionGroup.a 1
  | 2 => QuaternionGroup.a 2
  | 3 => QuaternionGroup.a 3
  | 4 => QuaternionGroup.xa 0
  | 5 => QuaternionGroup.xa 1
  | 6 => QuaternionGroup.xa 2
  | _ => QuaternionGroup.xa 3

@[expose] def encQ : Q → Nat
  | QuaternionGroup.a j => j.val
  | QuaternionGroup.xa j => 4 + j.val

@[expose] def enc (x : X) : Nat :=
  (((encQ x.1.1 * 8 + encQ x.1.2.1) * 8 + encQ x.1.2.2) * 2 + x.2.1.toNat) * 2 + x.2.2.toNat

@[expose] def dec (c : Nat) : X :=
  ((decQ (c / 256 % 8), decQ (c / 32 % 8), decQ (c / 4 % 8)), c / 2 % 2 == 1, c % 2 == 1)

@[expose] def reps (ε : Bool) : List Nat := if ε then repsGood else repsBad

@[expose] def tab (ε : Bool) : List (Nat × Nat × Nat) := if ε then tabGood else tabBad

@[expose] def rep (ε : Bool) (k : Nat) : X := dec ((reps ε).getD k 0)

@[expose] def lookup (ε : Bool) (x : X) : Nat × Nat :=
  match (tab ε).find? (fun t => t.1 == enc x) with
  | some t => (t.2.1, t.2.2)
  | none => (17, 0)

@[expose] def epsv (x : X) : Bool × Bool × Bool × Bool :=
  (xor (chiQ x.1.1) (chiQ x.1.2.1), chiQ x.1.2.2, x.2.1, x.2.2)

@[expose] def linE (f : Fin 4 → Bool) (e : Bool × Bool × Bool × Bool) : Bool :=
  ((f 0 && e.1) ^^ (f 1 && e.2.1)) ^^ ((f 2 && e.2.2.1) ^^ (f 3 && e.2.2.2))

@[expose] def fvec (a b c d : Bool) (j : Fin 4) : Bool :=
  match j.val with
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

@[expose] def lin (f : Fin 4 → Bool) (x : X) : Bool := linE f (epsv x)

@[expose] def LinClass (ε : Bool) : Prop :=
  ∀ x : X, IsInv ε x →
    (lookup ε x).1 < 17 ∧
    KEq (star ε (dec (lookup ε x).2) (rep ε (lookup ε x).1)) (star ε x (dec (lookup ε x).2)) ∧
    epsv x = epsv (rep ε (lookup ε x).1)

instance (ε : Bool) : Decidable (LinClass ε) := by unfold LinClass; infer_instance

theorem linClass_good : LinClass true := by decide +kernel

theorem linClass_bad : LinClass false := by decide +kernel

@[expose] def StepOK (ε : Bool) (i j k : Nat) (a c : X) : Prop :=
  IsInv ε a ∧ IsInv ε c ∧ KEq (star ε a c) (star ε c a) ∧ ¬ KEq a c ∧ IsInv ε (star ε a c) ∧
    (lookup ε a).1 = i ∧ (lookup ε c).1 = j ∧ (lookup ε (star ε a c)).1 = k

instance (ε : Bool) (i j k : Nat) (a c : X) : Decidable (StepOK ε i j k a c) := by
  unfold StepOK; infer_instance

theorem step_eq (ε : Bool) (lc : LinClass ε) (P : X → Prop) (w : Nat → Bool)
    (hw : ∀ k, w k = true ↔ P (rep ε k))
    (hconj : ∀ g x y, KEq (star ε g x) (star ε y g) → (P x ↔ P y))
    (hpar : ∀ a c, IsInv ε a → IsInv ε c → KEq (star ε a c) (star ε c a) → ¬ KEq a c →
      (Xor (P a) (P c) ↔ P (star ε a c)))
    {i j k : Nat} {a c : X} (h : StepOK ε i j k a c) : w k = (w i ^^ w j) := by
  obtain ⟨ha, hc, hac, hne, hp, hi, hj, hk⟩ := h
  have h1 : P (rep ε (lookup ε a).1) ↔ P a := hconj _ _ _ (lc a ha).2.1
  have h2 : P (rep ε (lookup ε c).1) ↔ P c := hconj _ _ _ (lc c hc).2.1
  have h3 : P (rep ε (lookup ε (star ε a c)).1) ↔ P (star ε a c) :=
    hconj _ _ _ (lc _ hp).2.1
  rw [hi] at h1
  rw [hj] at h2
  rw [hk] at h3
  have h4 := hpar a c ha hc hac hne
  have hx : (w i ^^ w j) = true ↔ Xor (w i = true) (w j = true) := by
    cases w i <;> cases w j <;> simp [Xor]
  rw [Bool.eq_iff_iff, hx, hw k, hw i, hw j, h3, h1, h2]
  exact h4.symm

theorem lin_core_good (P : X → Prop)
    (hconj : ∀ g x y, KEq (star true g x) (star true y g) → (P x ↔ P y))
    (hpar : ∀ a c, IsInv true a → IsInv true c → KEq (star true a c) (star true c a) →
      ¬ KEq a c → (Xor (P a) (P c) ↔ P (star true a c))) :
    ∃ f : Fin 4 → Bool, ∀ x, IsInv true x → (P x ↔ lin f x = true) := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : Nat → Bool, ∀ k, w k = true ↔ P (rep true k) :=
    ⟨fun k => decide (P (rep true k)), fun k => by simp⟩
  have lc := linClass_good
  have e1 := step_eq true lc P w hw hconj hpar
    (show StepOK true 0 0 2 (dec 1) (dec 9) by decide +kernel)
  have e2 := step_eq true lc P w hw hconj hpar
    (show StepOK true 0 0 3 (dec 1) (dec 65) by decide +kernel)
  have e3 := step_eq true lc P w hw hconj hpar
    (show StepOK true 0 0 16 (dec 1) (dec 1753) by decide +kernel)
  have e4 := step_eq true lc P w hw hconj hpar
    (show StepOK true 1 1 8 (dec 2) (dec 306) by decide +kernel)
  have e5 := step_eq true lc P w hw hconj hpar
    (show StepOK true 1 7 4 (dec 2) (dec 292) by decide +kernel)
  have e6 := step_eq true lc P w hw hconj hpar
    (show StepOK true 0 4 6 (dec 1) (dec 294) by decide +kernel)
  have e7 := step_eq true lc P w hw hconj hpar
    (show StepOK true 0 6 5 (dec 1) (dec 1463) by decide +kernel)
  have e8 := step_eq true lc P w hw hconj hpar
    (show StepOK true 1 4 9 (dec 2) (dec 1446) by decide +kernel)
  have e9 := step_eq true lc P w hw hconj hpar
    (show StepOK true 1 4 15 (dec 2) (dec 1158) by decide +kernel)
  have e10 := step_eq true lc P w hw hconj hpar
    (show StepOK true 6 6 14 (dec 151) (dec 295) by decide +kernel)
  have e11 := step_eq true lc P w hw hconj hpar
    (show StepOK true 7 11 10 (dec 292) (dec 1200) by decide +kernel)
  have e12 := step_eq true lc P w hw hconj hpar
    (show StepOK true 8 10 12 (dec 304) (dec 1940) by decide +kernel)
  have e13 := step_eq true lc P w hw hconj hpar
    (show StepOK true 10 11 13 (dec 388) (dec 1200) by decide +kernel)
  have hall : ∀ k, k < 17 → w k = lin (fvec (w 11) (w 7) (w 1) (w 0)) (rep true k) := by
    intro k hk
    interval_cases k <;>
    · try simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13]
      generalize w 11 = p3
      generalize w 7 = p2
      generalize w 1 = p1
      generalize w 0 = p0
      revert p0 p1 p2 p3
      decide +kernel
  refine ⟨(fvec (w 11) (w 7) (w 1) (w 0)), fun x hx => ?_⟩
  obtain ⟨hk, hc, he⟩ := lc x hx
  have h1 : P (rep true (lookup true x).1) ↔ P x := hconj _ _ _ hc
  rw [← h1, ← hw, hall _ hk]
  simp only [lin, he]

theorem lin_core_bad (P : X → Prop)
    (hconj : ∀ g x y, KEq (star false g x) (star false y g) → (P x ↔ P y))
    (hpar : ∀ a c, IsInv false a → IsInv false c → KEq (star false a c) (star false c a) →
      ¬ KEq a c → (Xor (P a) (P c) ↔ P (star false a c))) :
    ∃ f : Fin 4 → Bool, ∀ x, IsInv false x → (P x ↔ lin f x = true) := by
  classical
  obtain ⟨w, hw⟩ : ∃ w : Nat → Bool, ∀ k, w k = true ↔ P (rep false k) :=
    ⟨fun k => decide (P (rep false k)), fun k => by simp⟩
  have lc := linClass_bad
  have e1 := step_eq false lc P w hw hconj hpar
    (show StepOK false 0 0 3 (dec 1) (dec 9) by decide +kernel)
  have e2 := step_eq false lc P w hw hconj hpar
    (show StepOK false 0 0 4 (dec 1) (dec 65) by decide +kernel)
  have e3 := step_eq false lc P w hw hconj hpar
    (show StepOK false 0 0 16 (dec 1) (dec 1753) by decide +kernel)
  have e4 := step_eq false lc P w hw hconj hpar
    (show StepOK false 0 1 2 (dec 1) (dec 2) by decide +kernel)
  have e5 := step_eq false lc P w hw hconj hpar
    (show StepOK false 0 2 6 (dec 1) (dec 1755) by decide +kernel)
  have e6 := step_eq false lc P w hw hconj hpar
    (show StepOK false 1 7 5 (dec 2) (dec 292) by decide +kernel)
  have e7 := step_eq false lc P w hw hconj hpar
    (show StepOK false 1 5 9 (dec 2) (dec 310) by decide +kernel)
  have e8 := step_eq false lc P w hw hconj hpar
    (show StepOK false 1 5 15 (dec 2) (dec 1158) by decide +kernel)
  have e9 := step_eq false lc P w hw hconj hpar
    (show StepOK false 1 6 8 (dec 2) (dec 306) by decide +kernel)
  have e10 := step_eq false lc P w hw hconj hpar
    (show StepOK false 2 2 14 (dec 3) (dec 1019) by decide +kernel)
  have e11 := step_eq false lc P w hw hconj hpar
    (show StepOK false 7 11 10 (dec 292) (dec 1200) by decide +kernel)
  have e12 := step_eq false lc P w hw hconj hpar
    (show StepOK false 8 10 12 (dec 304) (dec 1940) by decide +kernel)
  have e13 := step_eq false lc P w hw hconj hpar
    (show StepOK false 10 11 13 (dec 388) (dec 1200) by decide +kernel)
  have hall : ∀ k, k < 17 → w k = lin (fvec (w 11) (w 7) (w 1) (w 0)) (rep false k) := by
    intro k hk
    interval_cases k <;>
    · try simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13]
      generalize w 11 = p3
      generalize w 7 = p2
      generalize w 1 = p1
      generalize w 0 = p0
      revert p0 p1 p2 p3
      decide +kernel
  refine ⟨(fvec (w 11) (w 7) (w 1) (w 0)), fun x hx => ?_⟩
  obtain ⟨hk, hc, he⟩ := lc x hx
  have h1 : P (rep false (lookup false x).1) ↔ P x := hconj _ _ _ hc
  rw [← h1, ← hw, hall _ hk]
  simp only [lin, he]

theorem lin_core (ε : Bool) (P : X → Prop)
    (hconj : ∀ g x y, KEq (star ε g x) (star ε y g) → (P x ↔ P y))
    (hpar : ∀ a c, IsInv ε a → IsInv ε c → KEq (star ε a c) (star ε c a) → ¬ KEq a c →
      (Xor (P a) (P c) ↔ P (star ε a c))) :
    ∃ f : Fin 4 → Bool, ∀ x, IsInv ε x → (P x ↔ lin f x = true) := by
  cases ε
  · exact lin_core_bad P hconj hpar
  · exact lin_core_good P hconj hpar

end CFSG.OddStandard.SmallF3.FritzII.FzL59BLin
