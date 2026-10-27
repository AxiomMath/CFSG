module

public import Certificates.Data.Kernel.OpsK
public import CFSG.Certificates.Kernel.OpsHom
public import CFSG.Certificates.Kernel.Co1BMulSound
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.KC.OpsK

open CFSG.KC.Loop CFSG.SectionRank.Native CFSG.Sporadic.GLQ CFSG.KC.OpsHom

theorem forceB_eq (y : Nat) (k : Nat → Bool) : forceB y k = k y := by
  cases y <;> rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem nIf_eq (c : Bool) (t e : Nat) : Bool.rec (motive := fun _ => Nat) e t c =
    (if c then t else e) := by
  cases c <;> rfl

theorem powN_eq {V : Type} (O : Ops Nat V) : ∀ (f X e : Nat), e < f → powN O f X e = O.pow X e := by
  intro f
  induction f with
  | zero => intro X e he; exact absurd he (Nat.not_lt_zero e)
  | succ f ih =>
    intro X e he
    change Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat)
      (strictN (O.mul X X) fun X2 => strictN (powN O f X2 (Nat.div e 2)) fun Y =>
        Bool.rec (motive := fun _ => Nat) Y (O.mul X Y) (Nat.beq (Nat.mod e 2) 1)) X (Nat.beq e 1))
      O.one (Nat.beq e 0) = _
    rw [strictN_eq, strictN_eq, nIf_eq, nIf_eq, nIf_eq]
    unfold Ops.pow
    by_cases h0 : e = 0
    · simp [h0]
    by_cases h1 : e = 1
    · simp [h1]
    have e0 : Nat.beq e 0 = false := by cases h : Nat.beq e 0; rfl; exact absurd (Nat.eq_of_beq_eq_true h) h0
    have e1 : Nat.beq e 1 = false := by cases h : Nat.beq e 1; rfl; exact absurd (Nat.eq_of_beq_eq_true h) h1
    rw [e0, e1, ite_eq_right h0, ite_eq_right h1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [ih (O.mul X X) (Nat.div e 2) (by change e / 2 < f; omega)]
    have em : Nat.mod e 2 = e % 2 := rfl
    have ed : Nat.div e 2 = e / 2 := rfl
    rw [em, ed]
    by_cases ho : e % 2 = 1
    · simp [ho]
    · have : Nat.beq (e % 2) 1 = false := by
        cases h : Nat.beq (e % 2) 1; rfl; exact absurd (Nat.eq_of_beq_eq_true h) ho
      simp [ho, this]

theorem stepK_eq {V : Type} (O : Ops Nat V) (R : Array (Nat × Nat)) (k : Array (Nat × Nat) → Bool)
    (ins : Instr) : stepK O R k ins = k (Instr.runN O R ins) := by
  cases ins with
  | mu i j t =>
    change forceB _ (fun a => forceB _ fun b => k (R.setIfInBounds t (a, b))) = _
    rw [forceB_eq, forceB_eq]
    rfl
  | iv i t => rfl
  | pwr e i t =>
    change forceB _ (fun a => forceB _ fun b => k (R.setIfInBounds t (a, b))) = _
    rw [forceB_eq, forceB_eq, powN_eq O _ _ _ (Nat.lt_succ_self e),
      powN_eq O _ _ _ (Nat.lt_succ_self e)]
    rfl

theorem runK_eq {V : Type} (O : Ops Nat V) : ∀ (prog : List Instr) (R : Array (Nat × Nat))
    (k : Array (Nat × Nat) → Bool), runK O prog R k = k (runProgN O R prog)
  | [], _, _ => rfl
  | ins :: prog, R, k => by
    change stepK O R (fun R' => runK O prog R' k) ins = _
    rw [stepK_eq, runK_eq O prog]
    rfl

theorem forceL_eq : ∀ (xs : List Nat) (k : List Nat → Bool), forceL xs k = k xs
  | [], _ => rfl
  | x :: xs, k => by
    change forceB x (fun x' => forceL xs fun l => k (x' :: l)) = _
    rw [forceB_eq, forceL_eq xs]

open CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KC.F2W CFSG.Sporadic.SmallF2.Native CFSG.KLie.CT

theorem shl_one (n : Nat) : Nat.shiftLeft 1 n = 2 ^ n := Nat.one_shiftLeft n

theorem unpackR_idF (d : Nat) : unpackR d (idF d) = idRows d := by
  unfold unpackR idRows
  congr 1
  funext i
  rw [← rowF_eq]
  have hf : ∀ j < d, pw2 j < 2 ^ d := fun j hj => by
    rw [show pw2 j = 2 ^ j from Nat.one_shiftLeft j]
    exact Nat.pow_lt_pow_right (by omega) hj
  exact rowF_orN d (f := pw2) hf i.isLt

theorem testBit_field (w P i b : Nat) :
    (P / 2 ^ (w * i) % 2 ^ w).testBit b = (decide (b < w) && P.testBit (w * i + b)) := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm b]

theorem fields_eq_iff {w : Nat} (hw : 0 < w) (n P Q : Nat) :
    (∀ i < n, P / 2 ^ (w * i) % 2 ^ w = Q / 2 ^ (w * i) % 2 ^ w) ↔
      P % 2 ^ (w * n) = Q % 2 ^ (w * n) := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro p
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hp : p < w * n
    · have hi : p / w < n := (Nat.div_lt_iff_lt_mul hw).2 (by rw [Nat.mul_comm]; exact hp)
      have hb := congrArg (fun x => x.testBit (p % w)) (h (p / w) hi)
      simp only [testBit_field, Nat.mod_lt p hw, decide_true, Bool.true_and, Nat.div_add_mod] at hb
      rw [hb]
    · simp [hp]
  · intro h i hi
    apply Nat.eq_of_testBit_eq
    intro b
    rw [testBit_field, testBit_field]
    by_cases hb : b < w
    · have hlt : w * i + b < w * n := by
        have : w * (i + 1) ≤ w * n := Nat.mul_le_mul_left w hi
        rw [Nat.mul_succ] at this
        omega
      have h2 := congrArg (fun x => x.testBit (w * i + b)) h
      simp only [Nat.testBit_mod_two_pow, hlt, decide_true, Bool.true_and] at h2
      rw [h2]
    · simp [hb]

theorem beq_unpackR {d : Nat} (hd : 0 < d) (A B : Nat) :
    (unpackR d A == unpackR d B) = Nat.beq (A % 2 ^ (d * d)) (B % 2 ^ (d * d)) := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, Nat.beq_eq, ← fields_eq_iff hd d A B]
  constructor
  · intro h i hi
    have := congrArg (fun X : Array Nat => X[i]!) h
    simpa [unpackR, hi] using this
  · intro h
    exact congrArg (Array.ofFn (n := d)) (funext fun i => h i.val i.isLt)

theorem vne_eq (d u w : Nat) : ((List.range d).any fun j => u.testBit j != w.testBit j) =
    !Nat.beq (u % 2 ^ d) (w % 2 ^ d) := by
  by_cases h : u % 2 ^ d = w % 2 ^ d
  · have hb : Nat.beq (u % 2 ^ d) (w % 2 ^ d) = true := by rw [Nat.beq_eq]; exact h
    rw [hb]
    apply List.any_eq_false.2
    intro j hj
    have hj' := List.mem_range.1 hj
    have := congrArg (fun x => x.testBit j) h
    simp only [Nat.testBit_mod_two_pow, hj', decide_true, Bool.true_and] at this
    simp [this]
  · have hb : Nat.beq (u % 2 ^ d) (w % 2 ^ d) = false := by
      cases e : Nat.beq (u % 2 ^ d) (w % 2 ^ d); rfl; exact absurd (Nat.eq_of_beq_eq_true e) h
    rw [hb]
    apply List.any_eq_true.2
    by_contra hc
    apply h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hj : j < d
    · simp only [hj, decide_true, Bool.true_and]
      by_contra hne
      exact hc ⟨j, List.mem_range.2 hj, by simp [hne]⟩
    · simp [hj]

@[expose] noncomputable def hom2 (d : Nat) (hd : 0 < d) : Hom (ops2 d) (opsF2K d) where
  U := unpackR d
  W := id
  P _ := True
  Q _ := True
  mul _ _ := ⟨mulRows_unpackW d _ _, trivial⟩
  one := ⟨(unpackR_idF d).symm, trivial⟩
  eq _ _ := by
    change (unpackR d _ == unpackR d _) = Nat.beq (Nat.mod _ (Nat.shiftLeft 1 (Nat.mul d d)))
      (Nat.mod _ (Nat.shiftLeft 1 (Nat.mul d d)))
    rw [beq_unpackR hd, shl_one]
    rfl
  vmul _ _ := ⟨vecMulN_unpackR d _ _, trivial⟩
  unit _ := ⟨rfl, trivial⟩
  vne _ _ := by
    change ((List.range d).any fun j => _) = Bool.not (Nat.beq (Nat.mod _ (Nat.shiftLeft 1 d))
      (Nat.mod _ (Nat.shiftLeft 1 d)))
    rw [vne_eq, shl_one]
    rfl

end CFSG.KC.OpsK

end
