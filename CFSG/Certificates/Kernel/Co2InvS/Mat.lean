module

public import Certificates.Data.Kernel.Co2InvS
public import CFSG.Certificates.Kernel.Co1BMulSound
public import CFSG.Sporadic.Co2InvCheckInputs

set_option exponentiation.threshold 600

public section

namespace CFSG.KC.Co2InvS

open CFSG.KC.Loop CFSG.KC.F2W CFSG.KLie.CT CFSG.KC.M1F2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co2Inv CFSG.KC.Co1F2

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem letB_eq (y : Nat) (k : Nat → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem bIf_eq' (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = if c then t else e := by
  cases c <;> rfl

theorem nIf_eq' (c : Bool) (t e : Nat) : Bool.rec (motive := fun _ => Nat) e t c =
    if c then t else e := by
  cases c <;> rfl

theorem notK_eq (b : Bool) : notK b = !b := by
  cases b <;> rfl

theorem blt_iff {a b : Nat} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

theorem blt_false {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false := by
  cases e : Nat.blt a b
  · rfl
  · exact absurd (blt_iff.1 e) h

theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem iteT {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem iteF {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by
  simp [h]

theorem mulV_eq_mulW (A B : Nat) : mulV A B = mulW 22 A B := by
  unfold mulV
  rw [mulW_eq_rec]
  rfl

theorem mulRows_unpack (A B : Nat) :
    mulRows 22 (unpackR 22 A) (unpackR 22 B) = unpackR 22 (mulV A B) := by
  rw [mulV_eq_mulW, mulRows_unpackW]

theorem mulV_lt (A B : Nat) : mulV A B < 2 ^ 484 := by
  rw [mulV_eq_mulW, mulW_eq, mulF_eq_orN]
  exact orN_fields_lt (d := 22) (n := 22) fun i _ => vmF_lt 22 B (rowF 22 A i)

theorem unpack_get (M : Nat) {i : Nat} (hi : i < 22) : (unpackR 22 M)[i]! = M / 2 ^ (22 * i) % 2 ^ 22 := by
  rw [getElem!_pos _ i (by simp [unpackR, hi])]
  simp [unpackR]

theorem unpack_inj {A B : Nat} (hA : A < 2 ^ 484) (hB : B < 2 ^ 484)
    (h : unpackR 22 A = unpackR 22 B) : A = B := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 484
  · have hi : p / 22 < 22 := by omega
    have e := congrArg (fun X : Array Nat => X[p / 22]!) h
    simp only [unpack_get _ hi] at e
    have e2 := congrArg (fun x => x.testBit (p % 22)) e
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow] at e2
    have hp' : 22 * (p / 22) + p % 22 = p := Nat.div_add_mod p 22
    rw [Nat.add_comm (p % 22), hp'] at e2
    simpa [Nat.mod_lt p (by norm_num : 0 < 22)] using e2
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hB (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem unpack_beq {A B : Nat} (hA : A < 2 ^ 484) (hB : B < 2 ^ 484) :
    (unpackR 22 A == unpackR 22 B) = Nat.beq A B := by
  by_cases h : A = B
  · subst h
    rw [Nat.beq_refl]
    exact beq_self_eq_true _
  · have h2 : Nat.beq A B = false := by
      cases e : Nat.beq A B
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) h
    rw [h2, beq_eq_false_iff_ne]
    exact fun e => h (unpack_inj hA hB e)

theorem IDP_lt : IDP < 2 ^ 484 := by decide

theorem idRows_eq : idRows 22 = unpackR 22 IDP := by
  apply Array.ext
  · simp [idRows, unpackR]
  · intro i h1 h2
    have hi : i < 22 := by simpa [idRows] using h1
    simp only [idRows, unpackR, Array.getElem_ofFn]
    interval_cases i <;> decide

theorem wfRows_unpack (M : Nat) : wfRows (unpackR 22 M) = true := by
  simp only [wfRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
  refine ⟨by simp [unpackR], fun i hi => ?_⟩
  simp only [unpackR, Array.getElem_ofFn]
  exact Nat.mod_lt _ (by norm_num)

theorem andK_eq (a b : Bool) : andK a b = (a && b) := by
  cases a <;> rfl

theorem implK_eq (a b : Bool) : implK a b = (if a then b else true) := by
  cases a <;> rfl

theorem selN_eq (c : Bool) (t e : Nat) : selN c t e = if c then t else e := by
  cases c <;> rfl

theorem oddE_eq (e : Nat) : oddE e = (decide (0 < e) && e % 2 == 1) := by
  unfold oddE
  rw [andK_eq]
  have h2 : Nat.land e 1 = e % 2 := Nat.and_one_is_mod e
  have h1 : Nat.blt 0 e = decide (0 < e) := by
    by_cases h : 0 < e
    · rw [decide_eq_true h]
      exact blt_iff.2 h
    · rw [decide_eq_false h]
      cases e
      · rfl
      · omega
  rw [h1, h2]
  rfl

theorem involK_eq (X : Nat) : involK X = (Nat.beq (mulV X X) IDP && !Nat.beq X IDP) := by
  unfold involK
  rw [andK_eq, notK_eq]

theorem isInvolRows_unpack {X : Nat} (hX : X < 2 ^ 484) :
    isInvolRows (unpackR 22 X) = involK X := by
  have e1 : isInvolRows (unpackR 22 X) =
      ((unpackR 22 (mulV X X) == unpackR 22 IDP) && !(unpackR 22 X == unpackR 22 IDP)) := by
    unfold isInvolRows
    rw [mulRows_unpack, idRows_eq]
    rfl
  rw [e1, involK_eq, unpack_beq (mulV_lt X X) IDP_lt, unpack_beq hX IDP_lt]

theorem fip_unpack {Q : Nat} (hQ : Q < 2 ^ 484) : ∀ (fuel P e : Nat), P < 2 ^ 484 → 0 < e →
    firstIdPow (unpackR 22 Q) fuel (unpackR 22 P) e =
      if fipK Q fuel P e = 0 then none else some (fipK Q fuel P e)
  | 0, P, e, _, _ => by simp [firstIdPow, fipK]
  | fuel + 1, P, e, hP, he => by
    have h1 : fipK Q (fuel + 1) P e = if Nat.beq P IDP then e else fipK Q fuel (mulV P Q) (e + 1) := by
      change selN (Nat.beq P IDP) e (strictN (mulV P Q) fun P' => fipK Q fuel P' (e + 1)) = _
      rw [selN_eq, strictN_eq']
    rw [firstIdPow, h1, idRows_eq, unpack_beq hP IDP_lt]
    cases Nat.beq P IDP
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [mulRows_unpack]
      exact fip_unpack hQ fuel _ _ (mulV_lt P Q) (by omega)
    · simp only [↓reduceIte]
      rw [iteF (by omega)]

theorem oddPowOK_unpack {Q : Nat} (hQ : Q < 2 ^ 484) :
    oddPowOK (unpackR 22 Q) = oddK Q := by
  have hp : powRows 22 (unpackR 22 Q) 1 = unpackR 22 (mulV IDP Q) := by
    rw [powRows, powRows, idRows_eq, mulRows_unpack]
  rw [oddPowOK, hp, fip_unpack hQ 64 _ 1 (mulV_lt IDP Q) (by norm_num), oddK]
  generalize fipK Q 64 (mulV IDP Q) 1 = e
  rw [oddE_eq]
  by_cases h : e = 0
  · subst h
    rfl
  · rw [iteF h]
    dsimp only
    rw [decide_eq_true (by omega : 0 < e), Bool.true_and]

end CFSG.KC.Co2InvS

end
